// kafueineto — keep a Mac awake and, in explicit aggressive mode, keep the
// current GUI session from being auto-locked.
//
// Build (a current macOS SDK; runtime -a support also requires sysadminctl -screenLock; C++17 and Blocks are required):
//   clang++ -std=c++17 -O2 -Wall -Wextra -Wpedantic -fblocks \
//     kafueineto.cpp -o kafueineto \
//     -framework ApplicationServices -framework IOKit \
//     -framework SystemConfiguration -framework CoreFoundation -lutil
//
// Modes (the idle-sleep veto and, with -d, periodic user activity come with
// every mode):
//   Default             Prevent idle system sleep with an IOKit assertion.
//   -d / --display      Also prevent idle display sleep and declare activity.
//   -x / --max          Every layer that needs no privilege: -d, the strong
//                       PreventSystemSleep assertion, input jiggle, and the
//                       Accessibility permission request.
//   -H / --hard-no-sleep  Root-only. Additionally set the system-wide
//                       SleepDisabled gate (and hold the strong assertion).
//   -a / --all          Root-only. -x and -H plus temporary Screen Lock/
//                       screensaver policy overrides for the logged-in GUI
//                       user.
//
// Persistent settings are snapshotted before modification, and unreadable
// snapshots prevent activation. Floating preferences are compared within the
// precision of defaults' text interface, not guaranteed bit-for-bit. A detached
// cleanup watchdog attempts restoration after normal exit, signals, parent crash,
// SIGKILL, or timeout. Because neither process survives a panic, power loss,
// or SIGKILL of both, the snapshot is also written to
// /var/db/kafueineto-policy.state before the first change and removed only
// once restoration is verified; while that file exists the root-only modes
// refuse to start, so a later run can never mistake half-restored state for
// the original. It lists the exact commands to restore by hand.
//
// In -a mode the user's login password is read from /dev/tty, never placed in
// argv/environment or the recovery file. Its main buffers are mlock()'d,
// core dumps are disabled, and both parent and watchdog explicitly wipe them.
// The authentication tool also receives the secret via a private terminal.
//
// Hard limits: this does not and must not auto-unlock an already locked session,
// bypass authentication or managed-device policy, prevent restart/shutdown,
// survive power loss, or override thermal/critical-battery safety. Running a
// closed portable Mac is a heat and battery hazard.

#include <ApplicationServices/ApplicationServices.h>
#include <IOKit/IOKitLib.h>
#include <IOKit/IOMessage.h>
#include <IOKit/ps/IOPSKeys.h>
#include <IOKit/ps/IOPowerSources.h>
#include <IOKit/pwr_mgt/IOPMLib.h>
#include <dispatch/dispatch.h>
#include <notify.h>
#include <SystemConfiguration/SystemConfiguration.h>

#include <cerrno>
#include <cstdarg>
#include <dirent.h>
#include <cmath>
#include <initializer_list>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <getopt.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <strings.h>
#include <sys/file.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <atomic>
#include <cctype>
#include <climits>
#include <grp.h>
#include <limits.h>
#include <limits>
#include <string_view>
#include <pwd.h>
#include <readpassphrase.h>
#include <string>
#include <vector>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <termios.h>
#include <util.h>

static const char *kVersion = "2.0.0";

// ---------------------------------------------------------------- config ---

struct Config {
    bool   all            = false;  // -a: aggressive no-sleep + no-auto-lock
    bool   max            = false;  // -x: every layer that works without root
    bool   display        = false;  // -d: also prevent display sleep
    bool   strong         = false;  // hold the PreventSystemSleep assertion
    bool   jiggle         = true;   // --no-jiggle disables input layer
    bool   noJiggleExplicit = false;
    bool   acOnly         = false;  // -A: hold assertions only on AC power
    bool   drift          = false;  // --drift: don't restore cursor position
    bool   requestPerm    = false;  // --request-permission: prompt for TCC
    bool   hardNoSleep    = false;  // -H: system-wide SleepDisabled
    bool   idleProbe      = false;  // diagnostic only; run after validation
    int    minBattery     = 0;      // -b: pause below this % when on battery
    double idleThreshold  = 120.0;  // -i: seconds of real idle before jiggle
    double timeout        = 0.0;    // -t: auto-exit after this many seconds
    pid_t  waitPid        = 0;      // -w: exit when this process exits
    int    verbose        = 0;      // -v
    bool   quiet          = false;  // -q
};

static Config cfg;

// ----------------------------------------------------------------- state ---

struct Assertion {
    CFStringRef  type;
    CFStringRef  name;
    const char  *label;
    IOPMAssertionID id = kIOPMNullAssertionID;
};

static Assertion gSystemAssertion  = {
    kIOPMAssertionTypePreventUserIdleSystemSleep,
    CFSTR("kafueineto: preventing idle system sleep"),
    "system-sleep",
};
static Assertion gDisplayAssertion = {
    kIOPMAssertionTypePreventUserIdleDisplaySleep,
    CFSTR("kafueineto: preventing idle display sleep"),
    "display-sleep",
};
static Assertion gStrongSystemAssertion = {
    // Deprecated in the SDK header, but powerd still tracks and honors the
    // "PreventSystemSleep" category (see `pmset -g assertions`); it is what
    // `caffeinate -s` creates. Held by -x, -H and -a.
    kIOPMAssertionTypePreventSystemSleep,
    CFSTR("kafueineto: preventing system sleep (strong assertion)"),
    "strong-system-sleep",
};

// Read from the power-notification queue for the sleep-veto decision while
// the main queue mutates it; hence atomic.
static std::atomic<bool>     gActive{false};            // assertions held?
static bool                  gWarnedNoPerm    = false;
static int64_t               gDeadline        = 0;      // monotonic ms for -t
static io_connect_t          gRootPort        = MACH_PORT_NULL;
static IONotificationPortRef gNotifyPort      = nullptr;
static io_object_t           gNotifier        = IO_OBJECT_NULL;
static IOPMAssertionID       gUserActivityID  = kIOPMNullAssertionID;
static CGEventSourceRef      gEventSource     = nullptr;
static dispatch_source_t     gTimer           = nullptr;
static uint64_t              gJiggleCount     = 0;
static int                   gHardGuardWrite  = -1;
static pid_t                 gHardGuardPid    = 0;
static int                   gPolicyLockFd    = -1;
static dispatch_queue_t      gMainQueue       = nullptr;
static dispatch_queue_t      gPowerQueue      = nullptr;
// Set in the forked watchdog: it must stay on plain syscalls and fork/exec,
// never CoreFoundation/IOKit, since a helper thread could have held a
// framework lock at fork time.
static bool                  gIsPolicyWatchdog = false;
static int                   gOriginalSleepDisabled = 0;
static bool                  gHardSleepApplied = false;
static volatile sig_atomic_t gHardGuardStop    = 0;
static bool                  gForceFullPolicyCheck = false;
static dispatch_source_t     gPreferenceWatchers[2] = {nullptr, nullptr};
static int                   gPreferenceWatchFDs[2] = {-1, -1};

// ------------------------------------------------------------------- log ---

static void logLine(FILE *to, const char *tag, const char *fmt, va_list ap) {
    char ts[32];
    time_t now = time(nullptr);
    struct tm tmv;
    localtime_r(&now, &tmv);
    strftime(ts, sizeof ts, "%H:%M:%S", &tmv);
    // One process-wide lock around the whole line: the power queue and the
    // main queue both log, and stdout/stderr usually share one tty, so a
    // per-FILE lock (flockfile) would still let an info and a warn
    // interleave mid-line.
    static pthread_mutex_t logMutex = PTHREAD_MUTEX_INITIALIZER;
    pthread_mutex_lock(&logMutex);
    flockfile(to);
    fprintf(to, "kafueineto %s %s", ts, tag);
    vfprintf(to, fmt, ap);
    fputc('\n', to);
    fflush(to);
    funlockfile(to);
    pthread_mutex_unlock(&logMutex);
}

__attribute__((format(printf, 1, 2)))
static void info(const char *fmt, ...) {
    if (cfg.quiet) return;
    va_list ap; va_start(ap, fmt);
    logLine(stdout, "", fmt, ap);
    va_end(ap);
}

__attribute__((format(printf, 1, 2)))
static void debug(const char *fmt, ...) {
    if (cfg.quiet || cfg.verbose < 1) return;
    va_list ap; va_start(ap, fmt);
    logLine(stdout, "· ", fmt, ap);
    va_end(ap);
}

__attribute__((format(printf, 1, 2)))
static void warn(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    logLine(stderr, "! ", fmt, ap);
    va_end(ap);
}

// --------------------------------------- persistent policy + rollback guard ---

struct CommandResult {
    bool launched = false;
    bool timedOut = false;
    bool outputTruncated = false;
    int exitCode = -1;
    std::string output;
};

struct ConsoleUser {
    bool valid = false;
    uid_t uid = (uid_t)-1;
    gid_t gid = (gid_t)-1;
    char name[256] = {};
    char home[PATH_MAX] = {};
    gid_t groups[128] = {};
    int groupCount = 0;
};

enum class LockKind { Invalid, Off, Immediate, Seconds };

struct LockMode {
    LockKind kind = LockKind::Invalid;
    int seconds = 0;
};

enum class PrefValueType { Unknown, Boolean, Integer, Float };

struct IntPrefSnapshot {
    const char *domain;
    const char *key;
    bool currentHost;
    bool valid = false;
    bool existed = false;
    double value = 0;
    PrefValueType type = PrefValueType::Unknown;
};

struct Secret {
    char bytes[1024] = {};
    size_t length = 0;
    bool locked = false;
};

static ConsoleUser gConsoleUser;
static LockMode gOriginalLockMode;
static IntPrefSnapshot gLockPrefs[] = {
    // Both ordinary and ByHost/currentHost stores are covered. macOS releases
    // have moved these keys over time, and managed/effective preferences can
    // expose either location.
    {"com.apple.screensaver", "askForPassword", false},
    {"com.apple.screensaver", "askForPassword", true},
    {"com.apple.screensaver", "askForPasswordDelay", false},
    {"com.apple.screensaver", "askForPasswordDelay", true},
    {"com.apple.screensaver", "idleTime", false},
    {"com.apple.screensaver", "idleTime", true},
};
static Secret gLoginPassword;
static bool gLockPolicyApplied = false;
static unsigned gPolicyFailures = 0;
static unsigned gConsecutiveDrifts = 0;
static unsigned gConsoleUserMisses = 0;
static uint64_t gAggressiveTicks = 0;
static bool gLastScreenLocked = false;

// Written with the full snapshot BEFORE the first persistent change and
// removed only after a verified restore, so a crash, panic, SIGKILL of both
// processes or power loss still leaves proof that the machine may be
// mutated — plus the values needed to repair it by hand. Arming refuses
// while it exists, so a later run can never snapshot half-mutated state as
// "original". /var/db survives reboot; /var/run is emptied at boot.
static const char *kPolicyStatePath = "/var/db/kafueineto-policy.state";

static void secureZero(void *ptr, size_t n) {
    volatile unsigned char *p = static_cast<volatile unsigned char *>(ptr);
    while (n--) *p++ = 0;
}

static void clearSecret(Secret *secret) {
    if (!secret) return;
    secureZero(secret->bytes, sizeof secret->bytes);
    secret->length = 0;
    if (secret->locked) {
        munlock(secret->bytes, sizeof secret->bytes);
        secret->locked = false;
    }
}


static bool waitForChild(pid_t pid, int *status) {
    pid_t r;
    do {
        r = waitpid(pid, status, 0);
    } while (r == -1 && errno == EINTR);
    return r == pid;
}

static bool setCloseOnExec(int fd) {
    int flags = fcntl(fd, F_GETFD);
    return flags != -1 && fcntl(fd, F_SETFD, flags | FD_CLOEXEC) != -1;
}

static bool setNonBlocking(int fd) {
    int flags = fcntl(fd, F_GETFL);
    return flags != -1 && fcntl(fd, F_SETFL, flags | O_NONBLOCK) != -1;
}

// Keep internal descriptors out of 0..2. Otherwise, starting with closed
// stdio lets dup2(stdin) overwrite the very pipe meant for stdout.
static bool prepareDescriptor(int *fd) {
    if (!fd || *fd < 0) return false;
    if (*fd <= STDERR_FILENO) {
        int moved = fcntl(*fd, F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
        if (moved == -1) return false;
        close(*fd);
        *fd = moved;
        return true;
    }
    return setCloseOnExec(*fd);
}

static bool createPipe(int fds[2]) {
    fds[0] = fds[1] = -1;
    if (pipe(fds) != 0) return false;
    if (prepareDescriptor(&fds[0]) && prepareDescriptor(&fds[1])) return true;
    int saved = errno;
    close(fds[0]); close(fds[1]);
    fds[0] = fds[1] = -1;
    errno = saved;
    return false;
}

static int64_t monotonicMilliseconds(void) {
    struct timespec ts = {};
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
        _exit(1);  // continuing with a frozen clock would disable timeouts
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int64_t durationMilliseconds(double seconds) {
    // Round UP to the next millisecond: never shorten a requested duration.
    return (int64_t)std::ceil(seconds * 1000.0);
}

// Returns true once the child was reaped; false if it is still running when
// the timeout passes (the caller decides whether to kill or abandon it).
static bool waitForChildTimed(pid_t pid, int *status, int timeoutMs,
                              bool *stillRunning = nullptr) {
    if (stillRunning) *stillRunning = false;
    int64_t deadline = monotonicMilliseconds() + timeoutMs;
    for (;;) {
        pid_t r = waitpid(pid, status, WNOHANG);
        if (r == pid) return true;
        // ECHILD means someone else reaped it; the pid is gone either way and
        // must never be signalled — it may already belong to a new process.
        if (r == -1 && errno != EINTR) return false;
        if (monotonicMilliseconds() >= deadline) {
            if (stillRunning) *stillRunning = true;
            return false;
        }
        int64_t left = deadline - monotonicMilliseconds();
        if (left > 0) poll(nullptr, 0, (int)std::min<int64_t>(100, left));
    }
}

static std::string lowerASCII(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(), [](unsigned char c) {
        return static_cast<char>(std::tolower(c));
    });
    return s;
}

static std::string trimASCII(const std::string &s) {
    size_t first = 0;
    while (first < s.size() && std::isspace((unsigned char)s[first])) first++;
    size_t last = s.size();
    while (last > first && std::isspace((unsigned char)s[last - 1])) last--;
    return s.substr(first, last - first);
}

static bool getConsoleIdentity(ConsoleUser *out) {
    if (!out) return false;
    uid_t uid = (uid_t)-1;
    gid_t gid = (gid_t)-1;
    CFStringRef name = SCDynamicStoreCopyConsoleUser(nullptr, &uid, &gid);
    if (!name) return false;
    char user[sizeof out->name] = {};
    bool converted = CFStringGetCString(name, user, sizeof user,
                                         kCFStringEncodingUTF8);
    CFRelease(name);
    if (!converted || uid == 0 || uid == (uid_t)-1 || gid == (gid_t)-1 ||
        user[0] == '\0' || !strcmp(user, "loginwindow") ||
        !strcmp(user, "_mbsetupuser"))
        return false;
    out->uid = uid;
    out->gid = gid;
    strlcpy(out->name, user, sizeof out->name);
    return true;
}

static bool getConsoleUser(ConsoleUser *out) {
    if (!out) return false;
    out->valid = false;
    if (!getConsoleIdentity(out)) return false;

    struct passwd pwd = {};
    struct passwd *result = nullptr;
    char buffer[16384];
    if (getpwuid_r(out->uid, &pwd, buffer, sizeof buffer, &result) != 0 ||
        !result || !result->pw_dir || result->pw_dir[0] != '/')
        return false;

    int groupCount = (int)(sizeof out->groups / sizeof out->groups[0]);
    if (getgrouplist(out->name, out->gid,
                     static_cast<int*>(static_cast<void*>(out->groups)),
                     &groupCount) == -1 || groupCount <= 0 ||
        groupCount > (int)(sizeof out->groups / sizeof out->groups[0]))
        return false;
    // setgroups() has a smaller limit than the directory membership list.
    if (groupCount > NGROUPS_MAX) groupCount = NGROUPS_MAX;
    if (strlcpy(out->home, result->pw_dir, sizeof out->home) >= sizeof out->home)
        return false;
    out->groupCount = groupCount;
    out->valid = true;
    return true;
}

static bool promptForPassword(const ConsoleUser &user, Secret *secret) {
    if (!secret) return false;

    struct rlimit coreLimit = {0, 0};
    if (setrlimit(RLIMIT_CORE, &coreLimit) != 0) {
        warn("could not disable core dumps; refusing to read a password: %s",
             strerror(errno));
        return false;
    }

    if (mlock(secret->bytes, sizeof secret->bytes) != 0) {
        warn("could not mlock the password buffer: %s", strerror(errno));
        return false;
    }
    secret->locked = true;

    char prompt[512];
    snprintf(prompt, sizeof prompt,
             "kafueineto: login password for %s (used only in locked memory "
             "to apply/restore Screen Lock): ",
             user.name);

    errno = 0;
    if (!readpassphrase(prompt, secret->bytes, sizeof secret->bytes,
                        RPP_ECHO_OFF | RPP_REQUIRE_TTY)) {
        warn("could not read the login password from /dev/tty: %s",
             errno ? strerror(errno) : "unknown error");
        clearSecret(secret);
        return false;
    }

    size_t used = strnlen(secret->bytes, sizeof secret->bytes);
    if (used == 0 || used >= sizeof secret->bytes - 1) {
        warn("%s", used == 0 ? "empty password not accepted"
                             : "password is too long");
        clearSecret(secret);
        return false;
    }
    secret->length = used;
    return true;
}

struct ExecArrays {
    std::vector<std::string> argStrings;
    std::vector<char *> argv;
    std::vector<std::string> envStrings;
    std::vector<char *> envp;
};

static ExecArrays makeExecArrays(const ConsoleUser &user,
                                 const std::vector<std::string> &args) {
    ExecArrays arrays;
    arrays.argStrings = args;
    arrays.argv.reserve(arrays.argStrings.size() + 1);
    for (std::string &s : arrays.argStrings)
        arrays.argv.push_back(const_cast<char *>(s.c_str()));
    arrays.argv.push_back(nullptr);

    arrays.envStrings.push_back(std::string("HOME=") + user.home);
    arrays.envStrings.push_back(std::string("USER=") + user.name);
    arrays.envStrings.push_back(std::string("LOGNAME=") + user.name);
    arrays.envStrings.push_back("PATH=/usr/bin:/bin:/usr/sbin:/sbin");
    arrays.envStrings.push_back("LANG=C");
    arrays.envStrings.push_back("LC_ALL=C");
    arrays.envStrings.push_back("TERM=dumb");
    char encoding[80];
    snprintf(encoding, sizeof encoding, "__CF_USER_TEXT_ENCODING=0x%X:0:0",
             (unsigned)user.uid);
    arrays.envStrings.push_back(encoding);

    arrays.envp.reserve(arrays.envStrings.size() + 1);
    for (std::string &s : arrays.envStrings)
        arrays.envp.push_back(const_cast<char *>(s.c_str()));
    arrays.envp.push_back(nullptr);
    return arrays;
}

static bool childBecomeUser(const ConsoleUser &user) {
    if (!user.valid) return false;
    // This child never needs the login password; drop the fork-copied (and
    // no-longer-mlocked) plaintext before it can outlive the exec.
    clearSecret(&gLoginPassword);
    // SIG_IGN dispositions survive execve (handlers do not), and this
    // process ignores all four; the tools we run must start with defaults or
    // they cannot be killed by an operator.
    for (int sig : {SIGPIPE, SIGINT, SIGTERM, SIGHUP})
        signal(sig, SIG_DFL);
    if (geteuid() == 0) {
        if (user.groupCount <= 0 ||
            setgroups(user.groupCount, user.groups) != 0)
            return false;
        if (setgid(user.gid) != 0) return false;
        if (setuid(user.uid) != 0) return false;
    } else if (geteuid() != user.uid) {
        return false;
    }
    if (chdir(user.home) != 0) return false;
    umask(077);
    return true;
}

static CommandResult collectChild(pid_t pid, int fd, int timeoutMs,
                                  bool pseudoTerminal) {
    CommandResult result;
    result.launched = true;
    // Reserve the whole cap up front: the password path wipes this buffer,
    // and geometric growth would leave un-zeroed copies behind in freed
    // heap blocks.
    result.output.reserve(65536);
    if (!setNonBlocking(fd)) {
        int ignored = 0;
        kill(pid, SIGKILL);
        waitForChild(pid, &ignored);
        close(fd);
        return result;
    }

    int status = 0;
    bool childDone = false;
    bool waitError = false;
    bool readError = false;
    bool eof = false;
    int64_t deadline = monotonicMilliseconds() + timeoutMs;
    int64_t drainDeadline = 0;

    char buffer[4096];
    while (!childDone || !eof) {
        // A continuously writing child must not starve waitpid/deadline
        // checks. Drain at most 64 KiB per turn, even after the output cap.
        for (unsigned reads = 0; reads < 16 && !eof; ++reads) {
            ssize_t n = read(fd, buffer, sizeof buffer);
            if (n > 0) {
                size_t room = 65536 - result.output.size();
                size_t kept = std::min(room, (size_t)n);
                result.output.append(buffer, kept);
                if (kept != (size_t)n) result.outputTruncated = true;
                continue;
            }
            if (n == 0 || (n == -1 && pseudoTerminal && errno == EIO))
                eof = true;
            if (n == -1 && errno == EINTR) continue;
            if (n == -1 && !eof && errno != EAGAIN && errno != EWOULDBLOCK) {
                readError = true;
                eof = true;
            }
            break;
        }

        if (!childDone) {
            pid_t r = waitpid(pid, &status, WNOHANG);
            if (r == pid) childDone = true;
            else if (r == -1 && errno != EINTR) {
                waitError = true;
                childDone = true;
            }
        }
        if (childDone && eof) break;

        int64_t now = monotonicMilliseconds();
        if (!childDone && now >= deadline) {
            result.timedOut = true;
            kill(pid, SIGKILL);
            if (!waitForChild(pid, &status)) waitError = true;
            childDone = true;
        }
        if (childDone && !eof) {
            // A pipe/pty can report EOF one scheduling turn after waitpid
            // observes the exit — but a grandchild that inherited the write
            // end can also hold EOF off forever. Drain briefly, then stop.
            if (drainDeadline == 0) drainDeadline = now + 2000;
            else if (now >= drainDeadline) break;
        }

        struct pollfd pfd = {fd, POLLIN | POLLHUP | POLLERR, 0};
        int64_t waitUntil = childDone ? drainDeadline : deadline;
        int waitMs = (int)std::min<int64_t>(100, waitUntil - now);
        if (waitMs < 0) waitMs = 0;
        // Once EOF is seen, a drained-pipe POLLHUP would return immediately
        // forever (a hot spin); sleep plainly and wait on the child instead.
        int pr;
        pr = poll(eof ? nullptr : &pfd, eof ? 0 : 1, waitMs);
        // Re-enter the outer loop on EINTR, so signals cannot keep resetting
        // a relative wait without checking the absolute deadline.
        if (pr == -1 && errno != EINTR) {
            readError = true;
            eof = true;
        }
        if (pr > 0 && (pfd.revents & POLLNVAL)) readError = true;
        if (pr > 0 && (pfd.revents & (POLLHUP | POLLERR | POLLNVAL)) &&
            !(pfd.revents & POLLIN))
            eof = true;
    }

    secureZero(buffer, sizeof buffer);
    close(fd);
    if (!childDone) waitForChild(pid, &status);
    if (!waitError && !readError && WIFEXITED(status))
        result.exitCode = WEXITSTATUS(status);
    else if (!waitError && !readError && WIFSIGNALED(status))
        result.exitCode = 128 + WTERMSIG(status);
    return result;
}

static CommandResult runCapturedAsUser(const ConsoleUser &user,
                                       const std::vector<std::string> &args,
                                       int timeoutMs = 10000) {
    CommandResult failed;
    if (args.empty()) return failed;

    ExecArrays arrays = makeExecArrays(user, args);
    char **argvp = arrays.argv.data();
    char **envpp = arrays.envp.data();
    const char *path = argvp[0];
    int output[2];
    if (!createPipe(output)) return failed;
    int nullFd = open("/dev/null", O_RDONLY | O_CLOEXEC);
    if (nullFd == -1 || !prepareDescriptor(&nullFd)) {
        if (nullFd != -1) close(nullFd);
        close(output[0]); close(output[1]);
        return failed;
    }

    pid_t pid = fork();
    if (pid == -1) {
        close(nullFd); close(output[0]); close(output[1]);
        return failed;
    }
    if (pid == 0) {
        close(output[0]);
        if (dup2(nullFd, STDIN_FILENO) == -1 ||
            dup2(output[1], STDOUT_FILENO) == -1 ||
            dup2(output[1], STDERR_FILENO) == -1)
            _exit(126);
        // A self-dup2 (possible when this process started with closed stdio)
        // does not clear FD_CLOEXEC; clear it so exec keeps fds 0-2 open.
        for (int f = STDIN_FILENO; f <= STDERR_FILENO; f++) {
            int flags = fcntl(f, F_GETFD);
            if (flags != -1) fcntl(f, F_SETFD, flags & ~FD_CLOEXEC);
        }
        if (nullFd > STDERR_FILENO) close(nullFd);
        if (output[1] > STDERR_FILENO) close(output[1]);
        if (!childBecomeUser(user)) _exit(126);
        execve(path, argvp, envpp);
        _exit(127);
    }

    close(nullFd);
    close(output[1]);
    return collectChild(pid, output[0], timeoutMs, false);
}

static bool writeAll(int fd, const void *buffer, size_t size) {
    const char *p = static_cast<const char *>(buffer);
    while (size > 0) {
        ssize_t n = write(fd, p, size);
        if (n > 0) {
            p += n;
            size -= (size_t)n;
            continue;
        }
        if (n == -1 && errno == EINTR) continue;
        if (n == -1 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            struct pollfd pfd = {fd, POLLOUT, 0};
            if (poll(&pfd, 1, 1000) > 0) continue;
        }
        return false;
    }
    return true;
}

static CommandResult runPasswordCommandAsUser(
    const ConsoleUser &user, const Secret &password,
    const std::vector<std::string> &args, int timeoutMs = 20000) {
    CommandResult failed;
    if (args.empty() || password.length == 0) return failed;

    ExecArrays arrays = makeExecArrays(user, args);
    char **argvp = arrays.argv.data();
    char **envpp = arrays.envp.data();
    const char *path = argvp[0];
    int master = -1, slave = -1;
    if (openpty(&master, &slave, nullptr, nullptr, nullptr) != 0)
        return failed;
    if (!prepareDescriptor(&master) || !prepareDescriptor(&slave)) {
        close(master); close(slave);
        return failed;
    }

    // Echo-off is mandatory, not best-effort: with ECHO left on, the
    // password written to the master would be reflected straight back into
    // the captured output.
    struct termios term = {};
    if (tcgetattr(slave, &term) != 0) {
        close(master); close(slave);
        return failed;
    }
    term.c_lflag &= ~(ECHO | ECHONL);
    if (tcsetattr(slave, TCSANOW, &term) != 0) {
        close(master); close(slave);
        return failed;
    }

    pid_t pid = fork();
    if (pid == -1) {
        close(master); close(slave);
        return failed;
    }
    if (pid == 0) {
        close(master);
        if (setsid() == -1) _exit(126);
        (void)ioctl(slave, TIOCSCTTY, 0);
        if (dup2(slave, STDIN_FILENO) == -1 ||
            dup2(slave, STDOUT_FILENO) == -1 ||
            dup2(slave, STDERR_FILENO) == -1)
            _exit(126);
        for (int f = STDIN_FILENO; f <= STDERR_FILENO; f++) {
            int flags = fcntl(f, F_GETFD);
            if (flags != -1) fcntl(f, F_SETFD, flags & ~FD_CLOEXEC);
        }
        if (slave > STDERR_FILENO) close(slave);
        if (!childBecomeUser(user)) _exit(126);
        execve(path, argvp, envpp);
        _exit(127);
    }

    close(slave);
    bool sent = writeAll(master, password.bytes, password.length) &&
                writeAll(master, "\n", 1);
    if (!sent) {
        kill(pid, SIGKILL);
        int ignored = 0;
        waitForChild(pid, &ignored);
        close(master);
        return failed;
    }
    CommandResult r = collectChild(pid, master, timeoutMs, true);
    // The exec'd tool owns the pty and can re-enable echo; treat the whole
    // transcript as though it may contain the password.
    if (!r.output.empty()) {
        secureZero(&r.output[0], r.output.size());
        r.output.clear();
    }
    return r;
}

static bool runPmsetSleepDisabled(int value) {
    pid_t pid = fork();
    if (pid == -1) return false;
    if (pid == 0) {
        clearSecret(&gLoginPassword);
        for (int sig : {SIGPIPE, SIGINT, SIGTERM, SIGHUP})
            signal(sig, SIG_DFL);
        execl("/usr/bin/pmset", "pmset", "-a", "disablesleep",
              value ? "1" : "0", (char *)nullptr);
        _exit(127);
    }

    int status = 0;
    bool stillRunning = false;
    if (!waitForChildTimed(pid, &status, 15000, &stillRunning)) {
        // A wedged pmset must not pin the queue that answers powerd. Only
        // signal it if it is genuinely still ours to signal.
        if (stillRunning) {
            kill(pid, SIGKILL);
            waitForChild(pid, &status);
        }
        return false;
    }
    return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

static int kernelSleepDisabled(void);

// Pure text scan over `pmset -g` output, separate so tests can feed it
// captured transcripts. The key must start its line (only blanks before
// it): an unanchored substring match would let some future
// "…SleepDisabled" row shadow the real one. Of the anchored rows the LAST
// wins, matching pmset's own last-wins semantics, and the number must sit
// on the same line as the key.
static bool parseSleepDisabledOutput(const std::string &output, int *value,
                                     bool *malformed = nullptr) {
    if (malformed) *malformed = false;
    if (!value || output.find('\0') != std::string::npos) {
        if (malformed) *malformed = true;
        return false;
    }
    constexpr std::string_view key = "SleepDisabled";
    std::string_view remaining(output);
    bool found = false;
    int parsed = 0;
    while (!remaining.empty()) {
        size_t end = remaining.find('\n');
        std::string_view line = remaining.substr(0, end);
        if (end == std::string_view::npos) remaining = {};
        else remaining.remove_prefix(end + 1);
        size_t first = line.find_first_not_of(" \t");
        if (first == std::string_view::npos) continue;
        line.remove_prefix(first);
        if (line.substr(0, key.size()) != key) continue;
        line.remove_prefix(key.size());
        // A different key with this prefix is not a SleepDisabled row.
        if (!line.empty() && line.front() != ' ' && line.front() != '\t' &&
            line.front() != '\r') continue;
        first = line.find_first_not_of(" \t\r");
        if (first == std::string_view::npos) {
            if (malformed) *malformed = true;
            return false;
        }
        line.remove_prefix(first);
        size_t last = line.find_last_not_of(" \t\r");
        line = line.substr(0, last + 1);
        // This is a boolean policy. Never normalize garbage or overflow to 1.
        if (line != "0" && line != "1") {
            if (malformed) *malformed = true;
            return false;
        }
        parsed = line.front() - '0';
        found = true;
    }
    if (found) *value = parsed;
    return found;
}

static bool readPmsetSleepDisabled(int *value) {
    int fds[2];
    if (!createPipe(fds)) return false;

    pid_t pid = fork();
    if (pid == -1) {
        close(fds[0]); close(fds[1]);
        return false;
    }
    if (pid == 0) {
        clearSecret(&gLoginPassword);
        close(fds[0]);
        if (dup2(fds[1], STDOUT_FILENO) == -1 ||
            dup2(fds[1], STDERR_FILENO) == -1)
            _exit(126);
        for (int f = STDOUT_FILENO; f <= STDERR_FILENO; f++) {
            int flags = fcntl(f, F_GETFD);
            if (flags != -1) fcntl(f, F_SETFD, flags & ~FD_CLOEXEC);
        }
        if (fds[1] > STDERR_FILENO) close(fds[1]);
        for (int sig : {SIGPIPE, SIGINT, SIGTERM, SIGHUP})
            signal(sig, SIG_DFL);
        execl("/usr/bin/pmset", "pmset", "-g", (char *)nullptr);
        _exit(127);
    }

    close(fds[1]);
    CommandResult r = collectChild(pid, fds[0], 15000, false);
    if (!r.launched || r.timedOut || r.outputTruncated || r.exitCode != 0)
        return false;

    bool malformed = false;
    if (parseSleepDisabledOutput(r.output, value, &malformed)) return true;
    if (malformed) return false;  // corrupt output is not an absent setting
    // The line can be absent; never assume 0 while SNAPSHOTTING (a snapshot
    // of 0 would clear a genuinely set flag on restore). Ask the kernel
    // instead. The forked watchdog must stay off CoreFoundation/IOKit —
    // but it also only ever VERIFIES, never snapshots, and pmset ran
    // cleanly to get here yet reported no SleepDisabled row. The flag is
    // set through pmset itself, which then reports it, so a clean report
    // without the row means clear; returning "unknown" here instead would
    // leave the watchdog permanently unable to confirm restoration on such
    // a system, retaining the marker and refusing every future run.
    if (gIsPolicyWatchdog) {
        *value = 0;
        return true;
    }
    int kernel = kernelSleepDisabled();
    if (kernel < 0) return false;
    *value = kernel;
    return true;
}

static bool lockModesEqual(const LockMode &a, const LockMode &b) {
    return a.kind == b.kind &&
           (a.kind != LockKind::Seconds || a.seconds == b.seconds);
}

static const char *lockModeDescription(const LockMode &mode,
                                       char *buffer, size_t size) {
    switch (mode.kind) {
    case LockKind::Off: return "off";
    case LockKind::Immediate: return "immediate";
    case LockKind::Seconds:
        snprintf(buffer, size, "%d seconds", mode.seconds);
        return buffer;
    default: return "unknown";
    }
}

static std::string lockModeArgument(const LockMode &mode) {
    switch (mode.kind) {
    case LockKind::Off: return "off";
    case LockKind::Immediate: return "immediate";
    case LockKind::Seconds: return std::to_string(mode.seconds);
    default: return std::string();
    }
}

// Quote recovery commands literally, including unusual account names.
static std::string shellQuote(const std::string &s) {
    std::string quoted = "'";
    for (char c : s) {
        if (c == '\'') quoted += "'\\''";
        else quoted += c;
    }
    return quoted + "'";
}

// Record the snapshot before mutation. Refuse activation unless both data
// and the directory entry were synced; never overwrite previous recovery data.
static bool writePolicyStateMarker(void) {
    int fd = open(kPolicyStatePath,
                  O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd == -1) return false;

    std::string text =
        "kafueineto changed system policy and has not confirmed restoring it.\n"
        "Restore the values below by hand, then delete this file to re-arm.\n\n";
    text += "  sudo /usr/bin/pmset -a disablesleep " +
            std::to_string(gOriginalSleepDisabled) + "\n";
    if (cfg.all) {
        std::string arg = lockModeArgument(gOriginalLockMode);
        text += "  sudo -H -u " + shellQuote(gConsoleUser.name) +
                " /usr/sbin/sysadminctl -screenLock " +
                (arg.empty() ? "<unknown>" : arg) + " -password -\n";
        for (const IntPrefSnapshot &pref : gLockPrefs) {
            text += "  sudo -H -u " + shellQuote(gConsoleUser.name) +
                    " /usr/bin/defaults ";
            if (pref.currentHost) text += "-currentHost ";
            if (!pref.valid) {
                text += "read " + std::string(pref.domain) + " " +
                        pref.key + "   # snapshot unavailable\n";
                continue;
            }
            if (!pref.existed) {
                text += "delete " + std::string(pref.domain) + " " +
                        pref.key + "\n";
                continue;
            }
            char value[64];
            if (pref.type == PrefValueType::Boolean)
                snprintf(value, sizeof value, "-bool %s",
                         pref.value != 0 ? "true" : "false");
            else if (pref.type == PrefValueType::Float)
                snprintf(value, sizeof value, "-float %.17g", pref.value);
            else
                snprintf(value, sizeof value, "-int %lld",
                         (long long)llround(pref.value));
            text += "write " + std::string(pref.domain) + " " + pref.key +
                    " " + value + "\n";
        }
    }
    bool ok = writeAll(fd, text.data(), text.size()) && fsync(fd) == 0;
    if (ok) {
        // Also commit the directory entry. An open failure is not success.
        std::string path(kPolicyStatePath);
        size_t slash = path.rfind('/');
        std::string parent = slash == std::string::npos ? "."
                              : slash == 0 ? "/" : path.substr(0, slash);
        int dirFd = open(parent.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (dirFd == -1) ok = false;
        else {
            if (fsync(dirFd) != 0) ok = false;
            if (close(dirFd) != 0) ok = false;
        }
    }
#ifdef __APPLE__
    // fsync alone need not flush a drive's volatile write cache on macOS.
    if (ok && fcntl(fd, F_FULLFSYNC) == -1) ok = false;
#endif
    if (close(fd) != 0) ok = false;
    // A torn marker must not block the next run: nothing has been mutated
    // yet when this can fail, so removing it is always correct here.
    if (!ok) unlink(kPolicyStatePath);
    return ok;
}

static bool removePolicyStateMarker(void) {
    return unlink(kPolicyStatePath) == 0 || errno == ENOENT;
}

static bool parseLockMode(const std::string &text, LockMode *mode) {
    if (!mode || text.find('\0') != std::string::npos) return false;
    std::string lower = lowerASCII(text);
    static const char *const phrases[] = {
        "screen lock delay is", "screenlock delay is",
        "screen lock is", "screenlock is",
    };
    size_t tailStart = std::string::npos;
    for (const char *phrase : phrases) {
        size_t pos = lower.rfind(phrase);
        if (pos == std::string::npos) continue;
        size_t end = pos + strlen(phrase);
        if (tailStart == std::string::npos || end > tailStart)
            tailStart = end;
    }
    if (tailStart == std::string::npos) return false;
    size_t eol = lower.find('\n', tailStart);
    std::string tail = trimASCII(lower.substr(tailStart, eol - tailStart));
    LockMode parsed;
    if (tail == "off" || tail == "disabled") parsed.kind = LockKind::Off;
    else if (tail == "immediate") parsed.kind = LockKind::Immediate;
    else {
        // Start at the value itself, not the first digit in an error message.
        if (tail.empty() || !std::isdigit((unsigned char)tail[0])) return false;
        errno = 0;
        char *end = nullptr;
        long seconds = strtol(tail.c_str(), &end, 10);
        if (errno != 0 || seconds < 0 || seconds > INT_MAX) return false;
        if (*end && !std::isspace((unsigned char)*end)) return false;
        std::string unit = trimASCII(end);
        if (!unit.empty() && unit != "s" && unit != "sec" && unit != "secs" &&
            unit != "second" && unit != "seconds") return false;
        parsed.kind = seconds == 0 ? LockKind::Immediate : LockKind::Seconds;
        parsed.seconds = (int)seconds;
    }
    *mode = parsed;
    return true;
}

static bool readScreenLockMode(LockMode *mode) {
    CommandResult r = runCapturedAsUser(
        gConsoleUser,
        {"/usr/sbin/sysadminctl", "-screenLock", "status"});
    // sysadminctl is shipped by macOS but has no stable public man page;
    // some releases have printed a useful status while returning a non-zero
    // status. Trust only a successfully parsed result, never the exit code
    // alone.
    // exitCode -1 is a wait error and >= 128 means the tool died on a signal;
    // partial output from either must not be trusted as a snapshot.
    return r.launched && !r.timedOut && !r.outputTruncated && r.exitCode >= 0 &&
           r.exitCode < 126 && parseLockMode(r.output, mode);
}

static bool setScreenLockMode(const LockMode &mode) {
    std::string arg = lockModeArgument(mode);
    if (arg.empty()) return false;
    CommandResult r = runPasswordCommandAsUser(
        gConsoleUser, gLoginPassword,
        {"/usr/sbin/sysadminctl", "-screenLock", arg,
         "-password", "-"});
    if (!r.launched || r.timedOut) return false;
    LockMode actual;
    return readScreenLockMode(&actual) && lockModesEqual(actual, mode);
}

static bool parseNumericPreference(const std::string &text, double *value) {
    if (!value || text.find('\0') != std::string::npos) return false;
    std::string s = lowerASCII(trimASCII(text));
    if (s == "true" || s == "yes") { *value = 1; return true; }
    if (s == "false" || s == "no") { *value = 0; return true; }
    // strtod accepts C99 hex ("0x10"), which the integer classifier below
    // would wave past its round-trip check; defaults(1) never prints hex.
    size_t digits = (s.size() > 1 && (s[0] == '-' || s[0] == '+')) ? 1 : 0;
    if (s.size() > digits + 1 && s[digits] == '0' &&
        (s[digits + 1] == 'x' || s[digits + 1] == 'X'))
        return false;
    char *end = nullptr;
    errno = 0;
    double n = strtod(s.c_str(), &end);
    while (end && *end && std::isspace((unsigned char)*end)) end++;
    if (errno != 0 || end == s.c_str() || (end && *end != '\0') ||
        !std::isfinite(n))
        return false;

    // An integer must survive the double round-trip exactly, or restoring
    // the snapshot would silently rewrite the user's value (past 2^53 a
    // double cannot represent every integer). Refusing here refuses to arm,
    // which is the safe direction.
    bool integerText = !s.empty();
    for (size_t i = 0; i < s.size() && integerText; i++) {
        if (i == 0 && (s[i] == '-' || s[i] == '+')) {
            integerText = s.size() > 1;
            continue;
        }
        if (!std::isdigit((unsigned char)s[i])) integerText = false;
    }
    if (integerText) {
        errno = 0;
        char *intEnd = nullptr;
        long long exact = strtoll(s.c_str(), &intEnd, 10);
        if (errno != 0 || intEnd == s.c_str() || *intEnd != '\0')
            return false;
        // Cap BEFORE the cast: for text near LLONG_MAX, strtod rounds up to
        // 2^63 and casting that back is undefined behavior that saturates
        // to LLONG_MAX on arm64 — the one value the round-trip check must
        // catch would falsely pass through its own UB. Anything past 2^53
        // cannot round-trip a double anyway, so refuse it outright.
        const long long kMaxExactInt = 1LL << 53;
        if (exact > kMaxExactInt || exact < -kMaxExactInt ||
            (long long)n != exact)
            return false;
    }
    *value = n;
    return true;
}

static bool prefValuesEqual(PrefValueType type, double a, double b) {
    // Bool/int round-trip exactly. Floats pass through defaults' own
    // formatting/parsing, which may not preserve every bit.
    if (type == PrefValueType::Float)
        return fabs(a - b) <= 1e-6 * std::max(1.0, fabs(b));
    return a == b;
}

static bool readPreferenceType(const IntPrefSnapshot &pref,
                               PrefValueType *type) {
    std::vector<std::string> args = {"/usr/bin/defaults"};
    if (pref.currentHost) args.push_back("-currentHost");
    args.push_back("read-type");
    args.push_back(pref.domain);
    args.push_back(pref.key);
    CommandResult r = runCapturedAsUser(gConsoleUser, args);
    if (!r.launched || r.timedOut || r.outputTruncated || r.exitCode != 0)
        return false;
    std::string lower = lowerASCII(r.output);
    if (lower.find("boolean") != std::string::npos ||
        lower.find("bool") != std::string::npos) {
        *type = PrefValueType::Boolean;
        return true;
    }
    if (lower.find("integer") != std::string::npos ||
        lower.find("int") != std::string::npos) {
        *type = PrefValueType::Integer;
        return true;
    }
    if (lower.find("float") != std::string::npos ||
        lower.find("real") != std::string::npos ||
        lower.find("double") != std::string::npos) {
        *type = PrefValueType::Float;
        return true;
    }
    return false;
}

// `defaults` prints the same "Domain '...' not found." for a domain that
// truly has no plist and for one whose plist exists but cannot be read
// (corrupt, mid-atomic-replace, permission/IO error). Believing the latter
// would record "absent" and DELETE a live setting on restore, so confirm
// against the backing file before trusting that message.
static bool preferenceDomainFileMissing(const IntPrefSnapshot &pref) {
    char path[PATH_MAX];
    struct stat st;
    int written;
    if (!pref.currentHost) {
        written = snprintf(path, sizeof path, "%s/Library/Preferences/%s.plist",
                          gConsoleUser.home, pref.domain);
        // A truncated path could stat some other, absent file; "unconfirmed"
        // must read as "present".
        if (written < 0 || (size_t)written >= sizeof path) return false;
        return lstat(path, &st) == -1 && errno == ENOENT;
    }
    // ByHost plists carry a per-host UUID suffix, so scan for the prefix —
    // case-insensitively: APFS folds case and Apple ships mixed-case ByHost
    // names side by side, so an exact-case scan could miss a live file that
    // CFPreferences happily reads.
    written = snprintf(path, sizeof path, "%s/Library/Preferences/ByHost",
                       gConsoleUser.home);
    if (written < 0 || (size_t)written >= sizeof path) return false;
    DIR *dir = opendir(path);
    if (!dir) return errno == ENOENT;
    size_t len = strlen(pref.domain);
    bool found = false;
    bool readError = false;
    for (;;) {
        errno = 0;
        const struct dirent *entry = readdir(dir);
        if (!entry) {
            // readdir reports both end-of-directory and failure as NULL; an
            // I/O error mid-scan is not proof of absence.
            readError = errno != 0;
            break;
        }
        if (strncasecmp(entry->d_name, pref.domain, len) == 0 &&
            entry->d_name[len] == '.') {
            found = true;
            break;
        }
    }
    closedir(dir);
    return !found && !readError;
}

static bool readPreference(IntPrefSnapshot *pref, bool captureType = false) {
    std::vector<std::string> args = {"/usr/bin/defaults"};
    if (pref->currentHost) args.push_back("-currentHost");
    args.push_back("read");
    args.push_back(pref->domain);
    args.push_back(pref->key);
    CommandResult r = runCapturedAsUser(gConsoleUser, args);
    if (!r.launched || r.timedOut || r.outputTruncated || r.exitCode < 0 ||
        r.exitCode >= 126) return false;
    if (r.exitCode != 0) {
        // Missing keys/domains have used several phrasings across macOS
        // releases: "The domain/default pair of (...) does not exist",
        // "Error: Could not find key '...' in domain '...'.", and
        // "Error: Domain '...' not found."
        std::string lower = lowerASCII(r.output);
        bool keyAbsent = lower.find("could not find key") != std::string::npos ||
                         (lower.find("domain/default pair") != std::string::npos &&
                          lower.find("does not exist") != std::string::npos);
        bool domainAbsent = (lower.find("does not exist") != std::string::npos ||
                             lower.find("not found") != std::string::npos) &&
                            preferenceDomainFileMissing(*pref);
        // "could not find key" is authoritative: defaults opened the domain.
        if (keyAbsent || domainAbsent) {
            pref->valid = true;
            pref->existed = false;
            pref->value = 0;
            pref->type = PrefValueType::Unknown;
            return true;
        }
        return false;
    }
    double value = 0;
    if (!parseNumericPreference(r.output, &value)) return false;
    PrefValueType type = pref->type;
    if (captureType && !readPreferenceType(*pref, &type)) return false;
    if (captureType &&
        ((type == PrefValueType::Boolean && value != 0 && value != 1) ||
         (type == PrefValueType::Integer &&
          (std::fabs(value) > 9007199254740992.0 || std::trunc(value) != value))))
        return false;
    // Commit only after every read succeeded, so a half-read can never pose
    // as a restorable snapshot.
    pref->valid = true;
    pref->existed = true;
    pref->value = value;
    pref->type = type;
    return true;
}

static bool queryPreference(const IntPrefSnapshot &pref, bool *exists,
                            double *value) {
    IntPrefSnapshot current = pref;
    current.valid = false;
    if (!readPreference(&current, false)) return false;
    *exists = current.existed;
    *value = current.value;
    return true;
}

static bool writePreference(const IntPrefSnapshot &pref, double value,
                            PrefValueType type) {
    if (!std::isfinite(value) ||
        (type == PrefValueType::Boolean && value != 0 && value != 1) ||
        (type == PrefValueType::Integer &&
         (std::fabs(value) > 9007199254740992.0 || std::trunc(value) != value)))
        return false;
    std::vector<std::string> args = {"/usr/bin/defaults"};
    if (pref.currentHost) args.push_back("-currentHost");
    args.push_back("write");
    args.push_back(pref.domain);
    args.push_back(pref.key);
    if (type == PrefValueType::Boolean) {
        args.push_back("-bool");
        args.push_back(value != 0 ? "true" : "false");
    } else if (type == PrefValueType::Integer) {
        args.push_back("-int");
        args.push_back(std::to_string((long long)llround(value)));
    } else if (type == PrefValueType::Float) {
        char buf[64];
        snprintf(buf, sizeof buf, "%.17g", value);
        args.push_back("-float");
        args.push_back(buf);
    } else {
        return false;
    }
    CommandResult r = runCapturedAsUser(gConsoleUser, args);
    if (!r.launched || r.timedOut || r.outputTruncated || r.exitCode != 0)
        return false;
    bool exists = false;
    double actual = 0;
    return queryPreference(pref, &exists, &actual) && exists &&
           prefValuesEqual(type, actual, value);
}

static bool deletePreference(const IntPrefSnapshot &pref) {
    bool exists = true;
    double ignored = 0;
    if (queryPreference(pref, &exists, &ignored) && !exists) return true;

    std::vector<std::string> args = {"/usr/bin/defaults"};
    if (pref.currentHost) args.push_back("-currentHost");
    args.push_back("delete");
    args.push_back(pref.domain);
    args.push_back(pref.key);
    CommandResult r = runCapturedAsUser(gConsoleUser, args);
    if (!r.launched || r.timedOut) return false;
    exists = true;
    return queryPreference(pref, &exists, &ignored) && !exists;
}

static double aggressivePreferenceValue(const IntPrefSnapshot &pref) {
    if (!strcmp(pref.key, "askForPassword")) return 0;
    if (!strcmp(pref.key, "askForPasswordDelay")) return INT_MAX;
    return 0;  // idleTime
}

static PrefValueType aggressivePreferenceType(const IntPrefSnapshot &pref) {
    return !strcmp(pref.key, "askForPassword")
               ? PrefValueType::Boolean
               : PrefValueType::Integer;
}

static bool applyAggressivePreferences(void) {
    bool ok = true;
    for (const IntPrefSnapshot &pref : gLockPrefs)
        ok = writePreference(pref, aggressivePreferenceValue(pref),
                             aggressivePreferenceType(pref)) && ok;
    return ok;
}

static bool restoreOriginalPreferences(void) {
    bool ok = true;
    for (const IntPrefSnapshot &pref : gLockPrefs) {
        if (!pref.valid) { ok = false; continue; }
        bool restored = pref.existed
                            ? writePreference(pref, pref.value, pref.type)
                            : deletePreference(pref);
        ok = restored && ok;
    }
    return ok;
}

static bool aggressivePreferencesAreSet(void) {
    for (const IntPrefSnapshot &pref : gLockPrefs) {
        bool exists = false;
        double value = 0;
        if (!queryPreference(pref, &exists, &value) || !exists ||
            !prefValuesEqual(aggressivePreferenceType(pref), value,
                             aggressivePreferenceValue(pref)))
            return false;
    }
    return true;
}

static bool applyAggressiveLockPolicy(void) {
    if (!cfg.all) return true;
    // Never mutate from an unrestorable snapshot, no matter how this was
    // reached — the startup abort is the first line, this is the invariant.
    if (gOriginalLockMode.kind == LockKind::Invalid) return false;
    for (const IntPrefSnapshot &pref : gLockPrefs)
        if (!pref.valid) return false;
    // Legacy/current-host preferences are secondary defense. The effective
    // modern lock policy is changed last and verified through sysadminctl.
    if (!applyAggressivePreferences()) return false;
    LockMode off;
    off.kind = LockKind::Off;
    if (!setScreenLockMode(off)) return false;
    gLockPolicyApplied = true;
    return true;
}

static bool restoreOriginalLockPolicy(void) {
    if (!cfg.all) return true;
    // Restore the effective password policy first so cleanup fails secure.
    bool modeOK = setScreenLockMode(gOriginalLockMode);
    bool prefsOK = restoreOriginalPreferences();
    if (modeOK && prefsOK) gLockPolicyApplied = false;
    return modeOK && prefsOK;
}

static bool repairAggressiveLockPolicy(const char *trigger, bool fullCheck) {
    if (!cfg.all) return true;
    if (gOriginalLockMode.kind == LockKind::Invalid) {
        // Unreachable while arming validates the snapshot; if it ever fires,
        // fail safe — but never silently into the 3-strike shutdown.
        warn("lock-policy repair invoked without a valid snapshot");
        return false;
    }

    LockMode current;
    LockMode off;
    off.kind = LockKind::Off;
    if (!readScreenLockMode(&current)) {
        warn("could not verify Screen Lock policy (%s)", trigger);
        return false;
    }
    bool modeDrift = !lockModesEqual(current, off);
    bool prefDrift = fullCheck && !aggressivePreferencesAreSet();
    if (!modeDrift && !prefDrift) {
        // Only a FULL check may clear the strike counter: a partial tick
        // cannot see preference drift, so letting it reset would keep an
        // externally-managed preference oscillating below the give-up
        // threshold forever.
        if (fullCheck) gConsecutiveDrifts = 0;
        return true;
    }

    if (++gConsecutiveDrifts >= 4) {
        // Something (managed policy?) reverts the policy faster than we can
        // repair it. Re-authenticating against that forever would hammer the
        // auth subsystem, so fail out through the strike counter instead.
        warn("lock policy keeps reverting externally (managed policy?); "
             "giving up rather than re-authenticating in a loop");
        return false;
    }

    bool ok = true;
    // Repair each layer with the narrowest action that fixes it: only a real
    // Screen Lock mode change is worth a password authentication.
    if (prefDrift) {
        warn("screen-saver preferences changed (%s); restoring aggressive "
             "values", trigger);
        ok = applyAggressivePreferences() && ok;
    }
    if (modeDrift) {
        char desc[64];
        warn("Screen Lock policy changed to %s (%s); reverting to off",
             lockModeDescription(current, desc, sizeof desc), trigger);
        ok = setScreenLockMode(off) && ok;
    }
    return ok;
}

static void policyGuardSignal(int) {
    gHardGuardStop = 1;
}

static bool originalPreferencesAreRestored(void) {
    for (const IntPrefSnapshot &pref : gLockPrefs) {
        IntPrefSnapshot current = pref;
        current.valid = false;
        current.type = PrefValueType::Unknown;
        if (!readPreference(&current, pref.existed)) return false;
        if (current.existed != pref.existed) return false;
        if (pref.existed &&
            (!prefValuesEqual(pref.type, current.value, pref.value) ||
             current.type != pref.type))
            return false;
    }
    return true;
}

static bool persistentPolicyMatchesSnapshot(void) {
    int sleepDisabled = -1;
    if (!readPmsetSleepDisabled(&sleepDisabled) ||
        sleepDisabled != gOriginalSleepDisabled)
        return false;

    if (cfg.all) {
        LockMode current;
        if (!readScreenLockMode(&current) ||
            !lockModesEqual(current, gOriginalLockMode) ||
            !originalPreferencesAreRestored())
            return false;
    }
    return true;
}

static bool restorePersistentPolicySnapshot(void) {
    bool ok = true;
    if (cfg.all) ok = restoreOriginalLockPolicy() && ok;
    // Guarded like every other persistent-layer accessor: without
    // --hard-no-sleep this never snapshotted SleepDisabled, so it must not
    // write a value it does not know.
    if (cfg.hardNoSleep)
        ok = runPmsetSleepDisabled(gOriginalSleepDisabled) && ok;
    return ok;
}

static void policyGuardWatchdog(int readFd, int lockFd, int readyFd,
                                int64_t deadline) {
    gIsPolicyWatchdog = true;
    bool ready = setsid() != -1;
    // A guard born already past its deadline must fail the handshake, not
    // arm-then-instantly-restore underneath a starting parent.
    if (deadline > 0 && monotonicMilliseconds() >= deadline) ready = false;
    if (cfg.all) {
        bool secretLocked =
            mlock(gLoginPassword.bytes, sizeof gLoginPassword.bytes) == 0;
        gLoginPassword.locked = secretLocked;
        ready = ready && secretLocked;
    }

    struct sigaction action = {};
    action.sa_handler = policyGuardSignal;
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;
    sigaction(SIGINT, &action, nullptr);
    sigaction(SIGTERM, &action, nullptr);
    sigaction(SIGHUP, &action, nullptr);
    sigaction(SIGQUIT, &action, nullptr);
    signal(SIGPIPE, SIG_IGN);

    char readyByte = ready ? 'R' : 'E';
    ssize_t readyWrite;
    do {
        readyWrite = write(readyFd, &readyByte, 1);
    } while (readyWrite == -1 && errno == EINTR);
    close(readyFd);
    if (!ready || readyWrite != 1) {
        clearSecret(&gLoginPassword);
        close(readFd);
        close(lockFd);
        _exit(2);
    }

    for (;;) {
        if (gHardGuardStop) break;
        int timeoutMs = -1;
        if (deadline > 0) {
            int64_t now = monotonicMilliseconds();
            if (now >= deadline) break;
            timeoutMs = (int)std::min<int64_t>(5000, deadline - now);
        }

        struct pollfd pfd = {readFd, POLLIN | POLLHUP | POLLERR, 0};
        int r;
        do {
            r = poll(&pfd, 1, timeoutMs);
        } while (r == -1 && errno == EINTR && !gHardGuardStop);

        if (gHardGuardStop) break;
        if (r == 0) continue;
        if (r < 0 || (pfd.revents & (POLLHUP | POLLERR | POLLNVAL))) break;
        if (pfd.revents & POLLIN) {
            char buffer[64];
            ssize_t n;
            do {
                n = read(readFd, buffer, sizeof buffer);
            } while (n == -1 && errno == EINTR);
            if (n <= 0) break;
        }
    }

    bool restored = persistentPolicyMatchesSnapshot();
    for (int attempt = 0; attempt < 5 && !restored; attempt++) {
        restored = restorePersistentPolicySnapshot() &&
                   persistentPolicyMatchesSnapshot();
        if (!restored) sleep(2);
    }

    // The marker (written before the first mutation) stays put unless the
    // snapshot is confirmed restored.
    if (restored) restored = removePolicyStateMarker();

    clearSecret(&gLoginPassword);
    close(readFd);
    close(lockFd);
    _exit(restored ? 0 : 1);
}

static bool startPolicyGuard(void) {
    if (!cfg.hardNoSleep) return true;
    if (geteuid() != 0) {
        warn("%s", cfg.all ? "-a requires root; run through sudo"
                           : "--hard-no-sleep requires root; run through sudo");
        return false;
    }

    // /var/db, not /var/run: /var/run is group-daemon writable, so any
    // daemon-group process could pre-create the lock and hold it to deny
    // arming forever. /var/db is root-only (and where the marker lives).
    int lockFd = open("/var/db/kafueineto-policy.lock",
                      O_RDWR | O_CREAT | O_NOFOLLOW, 0600);
    if (lockFd == -1 || flock(lockFd, LOCK_EX | LOCK_NB) != 0) {
        if (lockFd != -1) close(lockFd);
        warn("another kafueineto persistent-policy instance is active");
        return false;
    }
    if (!prepareDescriptor(&lockFd)) {
        warn("could not secure the policy lock descriptor: %s", strerror(errno));
        close(lockFd);
        return false;
    }

    struct stat marker = {};
    int markerStatus = lstat(kPolicyStatePath, &marker);
    if (markerStatus == 0 || errno != ENOENT) {
        // Arming on top of an unrestored session would snapshot the
        // half-mutated state as "original" and cement it.
        warn("a previous session did not confirm restoring the original "
             "policy; the values it needs are in %s — apply them, then "
             "delete that file to re-arm", kPolicyStatePath);
        close(lockFd);
        return false;
    }

    if (!readPmsetSleepDisabled(&gOriginalSleepDisabled)) {
        warn("could not read SleepDisabled; refusing a change that cannot be "
             "restored safely");
        close(lockFd);
        return false;
    }

    if (cfg.all) {
        if (!getConsoleUser(&gConsoleUser)) {
            warn("-a requires one logged-in GUI user");
            close(lockFd);
            return false;
        }
        if (!readScreenLockMode(&gOriginalLockMode)) {
            warn("could not read the effective Screen Lock policy; refusing "
                 "to change settings that could not be restored exactly");
            close(lockFd);
            return false;
        }
        for (IntPrefSnapshot &pref : gLockPrefs) {
            if (!readPreference(&pref, true)) {
                warn("could not snapshot %s/%s%s; refusing to change settings "
                     "that could not be restored exactly", pref.domain,
                     pref.key, pref.currentHost ? " (currentHost)" : "");
                close(lockFd);
                return false;
            }
        }
        if (!promptForPassword(gConsoleUser, &gLoginPassword)) {
            close(lockFd);
            return false;
        }
    }

    // Base the -t deadline only now: the password prompt above blocks for as
    // long as the user takes, and the budget must not start before arming.
    if (cfg.timeout > 0)
        gDeadline = monotonicMilliseconds() + durationMilliseconds(cfg.timeout);

    int guardPipe[2] = {-1, -1};
    int readyPipe[2] = {-1, -1};
    if (!createPipe(guardPipe) || !createPipe(readyPipe)) {
        warn("could not create cleanup watchdog: %s", strerror(errno));
        if (guardPipe[0] != -1) close(guardPipe[0]);
        if (guardPipe[1] != -1) close(guardPipe[1]);
        if (readyPipe[0] != -1) close(readyPipe[0]);
        if (readyPipe[1] != -1) close(readyPipe[1]);
        clearSecret(&gLoginPassword);
        close(lockFd);
        return false;
    }
    pid_t pid = fork();
    if (pid == -1) {
        warn("could not fork cleanup watchdog: %s", strerror(errno));
        close(guardPipe[0]); close(guardPipe[1]);
        close(readyPipe[0]); close(readyPipe[1]); close(lockFd);
        clearSecret(&gLoginPassword);
        return false;
    }
    if (pid == 0) {
        close(guardPipe[1]);
        close(readyPipe[0]);
        // Grace period: the parent owns the timeout, and the watchdog is a
        // backstop. Identical deadlines would have both restoring at once,
        // fighting each other's verification reads. -a teardown can spend
        // 20 s in sysadminctl's pty timeout plus several defaults writes,
        // so its grace must comfortably cover a full worst-case restore.
        int64_t grace = cfg.all ? 150000 : 45000;
        policyGuardWatchdog(guardPipe[0], lockFd, readyPipe[1],
                            gDeadline > 0 ? gDeadline + grace : 0);
    }

    close(guardPipe[0]);
    close(readyPipe[1]);

    char readyByte = 0;
    struct pollfd readyPoll = {readyPipe[0], POLLIN | POLLHUP | POLLERR, 0};
    int readyResult;
    do {
        readyResult = poll(&readyPoll, 1, 5000);
    } while (readyResult == -1 && errno == EINTR);
    ssize_t readyRead = -1;
    if (readyResult > 0 && (readyPoll.revents & POLLIN)) {
        do {
            readyRead = read(readyPipe[0], &readyByte, 1);
        } while (readyRead == -1 && errno == EINTR);
    }
    close(readyPipe[0]);

    if (readyRead != 1 || readyByte != 'R') {
        warn("cleanup watchdog failed its readiness/security check");
        close(guardPipe[1]);
        kill(pid, SIGKILL);
        int ignored = 0;
        waitForChild(pid, &ignored);
        close(lockFd);
        clearSecret(&gLoginPassword);
        return false;
    }

    // Keep our descriptor open for the process lifetime: the flock must hold
    // while EITHER this process or the watchdog is alive, or a second
    // instance could arm during the gap and snapshot the aggressive values
    // as "original".
    gPolicyLockFd = lockFd;
    gHardGuardWrite = guardPipe[1];
    gHardGuardPid = pid;

    // The guard is armed and the caller will now start mutating. Record the
    // snapshot so a panic, power loss, or SIGKILL of both processes still
    // leaves proof and repair instructions behind. This comes after every
    // arming-failure path above (a marker for a run that never mutated
    // anything would refuse to arm the next one), and mutating without a
    // durable marker would leave a hard kill unrecoverable — so on failure,
    // tear the just-armed watchdog down and refuse. Nothing has been
    // changed yet, so killing it outright is safe.
    if (!writePolicyStateMarker()) {
        warn("could not durably record the recovery snapshot in %s; "
             "refusing to change policy without it", kPolicyStatePath);
        close(gHardGuardWrite);
        gHardGuardWrite = -1;
        kill(pid, SIGKILL);
        int ignored = 0;
        waitForChild(pid, &ignored);
        gHardGuardPid = 0;
        gPolicyLockFd = -1;
        close(lockFd);
        clearSecret(&gLoginPassword);
        return false;
    }

    if (cfg.all) {
        char mode[64];
        info("aggressive rollback guard armed for user %s "
             "(original Screen Lock=%s, SleepDisabled=%d)",
             gConsoleUser.name,
             lockModeDescription(gOriginalLockMode, mode, sizeof mode),
             gOriginalSleepDisabled);
        warn("-a may keep a closed Mac running and disables automatic session "
             "locking while active; never put it in a bag or leave it "
             "unattended");
    } else {
        info("hard no-sleep guard armed (previous SleepDisabled=%d)",
             gOriginalSleepDisabled);
        warn("--hard-no-sleep may keep a closed Mac running; never put it in a "
             "bag or other unventilated space");
    }
    return true;
}

static bool setHardSleepDisabled(bool disabled) {
    if (!cfg.hardNoSleep || disabled == gHardSleepApplied) return true;
    int value = disabled ? 1 : gOriginalSleepDisabled;
    if (!runPmsetSleepDisabled(value)) {
        warn("pmset failed while setting SleepDisabled=%d", value);
        return false;
    }
    gHardSleepApplied = disabled;
    debug("SleepDisabled=%d (%s)", value,
          disabled ? "hard mode active" : "previous state restored");
    return true;
}

static int kernelSleepDisabled(void) {
    int result = -1;
    io_service_t root = IOServiceGetMatchingService(
        kIOMainPortDefault, IOServiceMatching("IOPMrootDomain"));
    if (root == IO_OBJECT_NULL) return result;

    CFTypeRef value = IORegistryEntryCreateCFProperty(
        root, CFSTR("SleepDisabled"), kCFAllocatorDefault, 0);
    if (value) {
        if (CFGetTypeID(value) == CFBooleanGetTypeID()) {
            result = CFBooleanGetValue((CFBooleanRef)value) ? 1 : 0;
        } else if (CFGetTypeID(value) == CFNumberGetTypeID()) {
            int n = 0;
            if (CFNumberGetValue((CFNumberRef)value, kCFNumberIntType, &n))
                result = n != 0 ? 1 : 0;
        }
        CFRelease(value);
    }
    IOObjectRelease(root);
    return result;
}

static bool policyGuardAlive(void) {
    if (!cfg.hardNoSleep) return true;
    if (gHardGuardPid <= 0) return false;

    int status = 0;
    pid_t r = waitpid(gHardGuardPid, &status, WNOHANG);
    if (r == 0 || (r == -1 && errno == EINTR)) return true;
    if (r == gHardGuardPid || (r == -1 && errno == ECHILD)) {
        if (gHardGuardWrite != -1) {
            close(gHardGuardWrite);
            gHardGuardWrite = -1;
        }
        gHardGuardPid = 0;
        return false;
    }
    return true;
}

// Returns false when restoration could not be confirmed, so the exit status
// reflects it — a wrapper script must be able to see that the machine may
// still be mutated.
static bool stopPolicyGuard(void) {
    bool confirmed = true;
    if (gHardGuardWrite != -1) {
        close(gHardGuardWrite);
        gHardGuardWrite = -1;
    }
    if (gHardGuardPid > 0) {
        int status = 0;
        // The watchdog independently verifies (and repairs) the snapshot; a
        // wedged repair must not pin this process forever, and killing the
        // restorer mid-restore would be worse — leave it running detached.
        if (!waitForChildTimed(gHardGuardPid, &status, 45000)) {
            warn("cleanup watchdog (pid %d) is still verifying restoration; "
                 "leaving it running", (int)gHardGuardPid);
            confirmed = false;
        } else if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
            warn("cleanup watchdog could not confirm complete restoration; "
                 "see %s", kPolicyStatePath);
            confirmed = false;
        }
        gHardGuardPid = 0;
    }
    clearSecret(&gLoginPassword);
    gHardSleepApplied = false;
    gLockPolicyApplied = false;
    return confirmed;
}

// ------------------------------------------------------------ assertions ---

static bool assertionAlive(IOPMAssertionID id) {
    if (id == kIOPMNullAssertionID) return false;
    CFDictionaryRef props = IOPMAssertionCopyProperties(id);
    if (!props) return false;
    CFRelease(props);
    return true;
}

static bool acquireAssertion(Assertion &a) {
    if (assertionAlive(a.id)) return true;
    if (a.id != kIOPMNullAssertionID) IOPMAssertionRelease(a.id);
    a.id = kIOPMNullAssertionID;

    CFMutableDictionaryRef props = CFDictionaryCreateMutable(
        kCFAllocatorDefault, 0, &kCFTypeDictionaryKeyCallBacks,
        &kCFTypeDictionaryValueCallBacks);
    if (!props) {
        warn("could not allocate %s assertion properties", a.label);
        return false;
    }
    CFDictionarySetValue(props, kIOPMAssertionTypeKey, a.type);
    CFDictionarySetValue(props, kIOPMAssertionNameKey, a.name);

    char detail[128];
    snprintf(detail, sizeof detail,
             "kafueineto pid %d; released on exit, signal, or timeout", getpid());
    CFStringRef detailStr = CFStringCreateWithCString(
        kCFAllocatorDefault, detail, kCFStringEncodingUTF8);
    if (detailStr) {
        CFDictionarySetValue(props, kIOPMAssertionDetailsKey, detailStr);
        CFRelease(detailStr);
    }

    // Let powerd expire assertions too, even if this process stops responding.
    if (gDeadline > 0) {
        // Past the deadline the next tick shuts down anyway; a 1 s floor keeps
        // a late acquire from failing (and aborting startup) for no benefit.
        double remaining = (gDeadline - monotonicMilliseconds()) / 1000.0;
        if (remaining < 1.0) remaining = 1.0;
        CFNumberRef timeoutNum = CFNumberCreate(kCFAllocatorDefault,
                                                kCFNumberDoubleType,
                                                &remaining);
        if (!timeoutNum) {
            CFRelease(props);
            warn("could not allocate %s assertion timeout", a.label);
            return false;
        }
        CFDictionarySetValue(props, kIOPMAssertionTimeoutKey, timeoutNum);
        CFDictionarySetValue(props, kIOPMAssertionTimeoutActionKey,
                             kIOPMAssertionTimeoutActionRelease);
        CFRelease(timeoutNum);
    }

    IOReturn r = IOPMAssertionCreateWithProperties(props, &a.id);
    CFRelease(props);
    if (r != kIOReturnSuccess || a.id == kIOPMNullAssertionID) {
        a.id = kIOPMNullAssertionID;
        warn("failed to create %s assertion (IOReturn 0x%x)", a.label, r);
        return false;
    }
    debug("%s assertion up (id %u)", a.label, a.id);
    return true;
}

static void releaseAssertion(Assertion &a) {
    if (a.id == kIOPMNullAssertionID) return;
    IOPMAssertionRelease(a.id);
    a.id = kIOPMNullAssertionID;
    debug("%s assertion released", a.label);
}

static bool screenLocked(void);

static void declareUserActivity(void) {
    // Refreshes the power-management notion of "a user is here" — keeps the
    // display undimmed without needing any TCC permission. Display mode only:
    // in system-only mode this would keep the screen lit against the user's
    // wishes. Never while locked or with the panel off: DeclareUserActivity
    // powers the display ON (stronger than the display assertion), and
    // relighting a locked screen every tick is hostile.
    if (screenLocked() || CGDisplayIsAsleep(CGMainDisplayID())) return;
    IOReturn r = IOPMAssertionDeclareUserActivity(
        CFSTR("kafueineto: periodic user-activity declaration"),
        kIOPMUserActiveLocal, &gUserActivityID);
    if (r != kIOReturnSuccess)
        debug("DeclareUserActivity failed (IOReturn 0x%x)", r);
}

static bool setActive(bool active, const char *why) {
    if (active == gActive) {
        bool ok = true;
        if (cfg.hardNoSleep && active && !gHardSleepApplied)
            ok = setHardSleepDisabled(true) && ok;
        if (cfg.hardNoSleep && !active && gHardSleepApplied)
            ok = setHardSleepDisabled(false) && ok;
        if (cfg.all && active && !gLockPolicyApplied)
            ok = applyAggressiveLockPolicy() && ok;
        if (cfg.all && !active && gLockPolicyApplied)
            ok = restoreOriginalLockPolicy() && ok;
        return ok;
    }

    if (active) {
        // Persistent gates first. The already-armed watchdog owns rollback if
        // this function fails halfway through or the parent is killed.
        if (cfg.hardNoSleep && !setHardSleepDisabled(true)) return false;
        if (cfg.all && !applyAggressiveLockPolicy()) {
            // A partial apply may already have landed (prefs written, mode
            // change unverified); undo what we can right away.
            (void)restoreOriginalLockPolicy();
            (void)setHardSleepDisabled(false);
            return false;
        }

        bool assertionsOK = acquireAssertion(gSystemAssertion);
        if (cfg.strong)
            assertionsOK = acquireAssertion(gStrongSystemAssertion) && assertionsOK;
        if (cfg.display)
            assertionsOK = acquireAssertion(gDisplayAssertion) && assertionsOK;
        if (!assertionsOK) {
            releaseAssertion(gSystemAssertion);
            releaseAssertion(gStrongSystemAssertion);
            releaseAssertion(gDisplayAssertion);
            (void)restoreOriginalLockPolicy();
            (void)setHardSleepDisabled(false);
            return false;
        }
        gActive = true;
        if (cfg.display) declareUserActivity();
        info("assertions up (%s)%s%s", why,
             cfg.hardNoSleep ? "; hard no-sleep active" : "",
             cfg.all ? "; automatic Screen Lock disabled" : "");
        return true;
    }

    gActive = false;

    // Restore while the watchdog is still armed and waiting. After this
    // returns, closing its lifetime pipe makes the watchdog independently
    // verify the snapshot and repair anything the parent could not restore.
    bool lockRestored = !cfg.all || restoreOriginalLockPolicy();

    releaseAssertion(gSystemAssertion);
    releaseAssertion(gStrongSystemAssertion);
    releaseAssertion(gDisplayAssertion);
    if (gUserActivityID != kIOPMNullAssertionID) {
        IOPMAssertionRelease(gUserActivityID);
        gUserActivityID = kIOPMNullAssertionID;
    }
    bool sleepRestored = !cfg.hardNoSleep || setHardSleepDisabled(false);
    info("assertions released (%s)%s%s", why,
         !cfg.hardNoSleep ? ""
         : sleepRestored ? "; previous sleep policy restored"
                         : "; watchdog will retry sleep restoration",
         !cfg.all ? ""
         : lockRestored ? "; previous Screen Lock policy restored"
                        : "; watchdog will retry Screen Lock restoration");
    return lockRestored && sleepRestored;
}

// ----------------------------------------------------------------- power ---

static bool onACPower(void) {
    CFTypeRef snapshot = IOPSCopyPowerSourcesInfo();
    if (!snapshot) return true;  // treat unknown as AC; desktops report no batteries
    CFStringRef type = IOPSGetProvidingPowerSourceType(snapshot);
    bool ac = !type || CFStringCompare(type, CFSTR(kIOPMACPowerKey), 0) ==
                           kCFCompareEqualTo;
    CFRelease(snapshot);
    return ac;
}

static int batteryPercent(void) {
    // Lowest internal-battery percentage, or 100 when there is no battery.
    int pct = 100;
    CFTypeRef snapshot = IOPSCopyPowerSourcesInfo();
    if (!snapshot) return pct;
    CFArrayRef list = IOPSCopyPowerSourcesList(snapshot);
    if (list) {
        for (CFIndex i = 0; i < CFArrayGetCount(list); i++) {
            CFDictionaryRef desc = IOPSGetPowerSourceDescription(
                snapshot, CFArrayGetValueAtIndex(list, i));
            if (!desc) continue;
            CFStringRef type = (CFStringRef)CFDictionaryGetValue(
                desc, CFSTR(kIOPSTypeKey));
            if (!type || CFStringCompare(type, CFSTR(kIOPSInternalBatteryType),
                                         0) != kCFCompareEqualTo)
                continue;  // a low UPS must not pause us
            CFNumberRef cur = (CFNumberRef)CFDictionaryGetValue(
                desc, CFSTR(kIOPSCurrentCapacityKey));
            CFNumberRef max = (CFNumberRef)CFDictionaryGetValue(
                desc, CFSTR(kIOPSMaxCapacityKey));
            int c = 0, m = 0;
            if (cur && max &&
                CFNumberGetValue(cur, kCFNumberIntType, &c) &&
                CFNumberGetValue(max, kCFNumberIntType, &m) && m > 0) {
                int p = (int)(100.0 * c / m + 0.5);
                if (p < pct) pct = p;
            }
        }
        CFRelease(list);
    }
    CFRelease(snapshot);
    return pct;
}

static int clamshellClosed(void) {
    int result = -1;
    io_service_t root = IOServiceGetMatchingService(
        kIOMainPortDefault, IOServiceMatching("IOPMrootDomain"));
    if (root == IO_OBJECT_NULL) return result;
    CFTypeRef value = IORegistryEntryCreateCFProperty(
        root, CFSTR("AppleClamshellState"), kCFAllocatorDefault, 0);
    if (value) {
        if (CFGetTypeID(value) == CFBooleanGetTypeID())
            result = CFBooleanGetValue((CFBooleanRef)value) ? 1 : 0;
        else if (CFGetTypeID(value) == CFNumberGetTypeID()) {
            int n = 0;
            if (CFNumberGetValue((CFNumberRef)value, kCFNumberIntType, &n))
                result = n != 0 ? 1 : 0;
        }
        CFRelease(value);
    }
    IOObjectRelease(root);
    return result;
}

// ------------------------------------------------------- idle + jiggling ---

static double userIdleSeconds(void) {
    // HID system state: the CGEventSource.h guidance for daemons, and
    // bit-identical to IORegistry HIDIdleTime. Events we post to the HID tap
    // reset it too, so the jiggle self-paces at exactly the threshold.
    return CGEventSourceSecondsSinceLastEventType(
        kCGEventSourceStateHIDSystemState, kCGAnyInputEventType);
}

static bool anyMouseButtonDown(void) {
    // HID state: physical buttons only — a synthetic press elsewhere in the
    // session shouldn't disable our drag guard's meaning.
    for (uint32_t b = 0; b < 32; b++) {
        if (CGEventSourceButtonState(kCGEventSourceStateHIDSystemState,
                                     (CGMouseButton)b))
            return true;
    }
    return false;
}

static bool screenLocked(void) {
    // "CGSSessionScreenIsLocked" is not declared in headers but has been
    // stable for many releases; missing key simply reads as unlocked.
    bool locked = false;
    CFDictionaryRef session = CGSessionCopyCurrentDictionary();
    if (session) {
        CFTypeRef v = CFDictionaryGetValue(session,
                                           CFSTR("CGSSessionScreenIsLocked"));
        locked = v && CFGetTypeID(v) == CFBooleanGetTypeID() &&
                 CFBooleanGetValue((CFBooleanRef)v);
        CFRelease(session);
    }
    return locked;
}

static bool canPostEvents(void) {
    return CGPreflightPostEventAccess();
}

static bool currentMouseLocation(CGPoint *out) {
    CGEventRef probe = CGEventCreate(nullptr);
    if (!probe) return false;
    *out = CGEventGetLocation(probe);
    CFRelease(probe);
    return true;
}

static void postMove(double x, double y) {
    CGEventRef e = CGEventCreateMouseEvent(gEventSource, kCGEventMouseMoved,
                                           CGPointMake(x, y),
                                           kCGMouseButtonLeft);
    if (e) {
        CGEventPost(kCGHIDEventTap, e);
        CFRelease(e);
    }
}

static void jiggleOnce(void) {
    CGPoint p;
    if (!currentMouseLocation(&p)) return;  // never jiggle from a guessed spot

    // Strictly 1px toward the center of the display under the cursor: an
    // inward move can neither leave the display, cross onto a neighbor, nor
    // step deeper into a hot corner — no clamping needed, and --drift
    // converges on the display center instead of an edge.
    double dx = -1.0;
    CGDirectDisplayID disp = kCGNullDirectDisplay;
    uint32_t nDisp = 0;
    if (CGGetDisplaysWithPoint(p, 1, &disp, &nDisp) == kCGErrorSuccess &&
        nDisp > 0) {
        CGRect b = CGDisplayBounds(disp);
        dx = (p.x < b.origin.x + b.size.width / 2) ? 1.0 : -1.0;
    } else if (p.x < 2.0) {
        dx = 1.0;
    }

    postMove(p.x + dx, p.y);

    // --drift leaves the cursor 1px displaced: a real position change per
    // jiggle, for the rare app that polls cursor coordinates instead of the
    // idle counters. Drift is bounded — every nudge points at the display
    // center.
    if (!cfg.drift) {
        usleep(25000);
        // Restore only if the cursor is still where we put it (epsilon
        // compare: Retina coordinates are fractional) — if the user moved it
        // meanwhile, yanking it back would be worse than a 1px offset.
        CGPoint q;
        if (currentMouseLocation(&q) &&
            fabs(q.x - (p.x + dx)) < 0.5 && fabs(q.y - p.y) < 0.5)
            postMove(p.x, p.y);
    }

    gJiggleCount++;
    debug("jiggle #%llu at (%.0f, %.0f)",
          (unsigned long long)gJiggleCount, p.x, p.y);
}

static void maybeJiggle(void) {
    if (!cfg.jiggle || !gActive) return;

    if (!canPostEvents()) {
        if (!gWarnedNoPerm) {
            warn("mouse jiggle unavailable: this process lacks permission to "
                 "post input events.");
            warn("grant it in System Settings > Privacy & Security > "
                 "Accessibility (add your terminal app, or kafueineto itself "
                 "when run from launchd), or rerun with --request-permission.");
            warn("open the pane directly: open "
                 "\"x-apple.systempreferences:com.apple.preference.security"
                 "?Privacy_Accessibility\"");
            warn("power assertions remain fully active without it.");
            gWarnedNoPerm = true;
        }
        return;
    }
    if (gWarnedNoPerm) {
        info("input-event permission granted; jiggle enabled");
        gWarnedNoPerm = false;
    }

    double idle = userIdleSeconds();
    if (idle < cfg.idleThreshold) {
        debug("idle %.0fs < %.0fs threshold; no jiggle", idle,
              cfg.idleThreshold);
        return;
    }
    if (anyMouseButtonDown()) {
        debug("mouse button held; skipping jiggle");
        return;
    }
    if (screenLocked()) {
        debug("screen locked; skipping jiggle");
        return;
    }
    if (CGDisplayIsAsleep(CGMainDisplayID())) {
        // A display that already went dark stays dark — waking it every
        // threshold seconds forever would be worse than any missed jiggle.
        debug("display asleep; skipping jiggle");
        return;
    }
    jiggleOnce();
}

// ----------------------------------------------------------- diagnostics ---

static double hidIdleSeconds(void) {
    // The IOKit-level idle counter (nanoseconds), as `ioreg -c IOHIDSystem`
    // reports it. Read here so tests can compare it against the
    // CGEventSource counter through one interface.
    double secs = -1.0;
    io_service_t svc = IOServiceGetMatchingService(
        kIOMainPortDefault, IOServiceMatching("IOHIDSystem"));
    if (svc != IO_OBJECT_NULL) {
        CFTypeRef v = IORegistryEntryCreateCFProperty(
            svc, CFSTR("HIDIdleTime"), kCFAllocatorDefault, 0);
        if (v) {
            int64_t ns = 0;
            if (CFGetTypeID(v) == CFNumberGetTypeID() &&
                CFNumberGetValue((CFNumberRef)v, kCFNumberSInt64Type, &ns))
                secs = (double)ns / 1e9;
            CFRelease(v);
        }
        IOObjectRelease(svc);
    }
    return secs;
}

static int idleProbe(void) {
    printf("session_idle_seconds\t%.3f\n",
           CGEventSourceSecondsSinceLastEventType(
               kCGEventSourceStateCombinedSessionState, kCGAnyInputEventType));
    printf("gate_idle_seconds\t%.3f\n", userIdleSeconds());
    printf("hid_idle_seconds\t%.3f\n", hidIdleSeconds());
    printf("can_post_events\t%s\n", canPostEvents() ? "yes" : "no");
    printf("screen_locked\t%s\n", screenLocked() ? "yes" : "no");
    printf("mouse_button_down\t%s\n", anyMouseButtonDown() ? "yes" : "no");
    printf("on_ac_power\t%s\n", onACPower() ? "yes" : "no");
    printf("battery_percent\t%d\n", batteryPercent());
    int clamshell = clamshellClosed();
    printf("clamshell_closed\t%s\n",
           clamshell < 0 ? "unknown" : clamshell ? "yes" : "no");
    CGPoint p;
    if (currentMouseLocation(&p))
        printf("cursor\t%.0f,%.0f\n", p.x, p.y);
    else
        printf("cursor\tunavailable\n");
    return 0;
}

// ------------------------------------------------------------- lifecycle ---

static void teardownPowerNotifications(void) {
    // Detach and drain first: a callback in flight on the power queue must
    // not touch the connection and port we are about to destroy.
    if (gNotifyPort && gPowerQueue) {
        IONotificationPortSetDispatchQueue(gNotifyPort, nullptr);
        dispatch_sync(gPowerQueue, ^{});
    }
    if (gRootPort != MACH_PORT_NULL) {
        IODeregisterForSystemPower(&gNotifier);
        IOServiceClose(gRootPort);
        gRootPort = MACH_PORT_NULL;
    }
    if (gNotifyPort) {
        IONotificationPortDestroy(gNotifyPort);
        gNotifyPort = nullptr;
    }
}

static bool policyGuardAlive(void);

static void shutdownNow(const char *reason, int code) {
    info("exiting: %s (%llu jiggle%s posted)", reason,
         (unsigned long long)gJiggleCount, gJiggleCount == 1 ? "" : "s");
    // Restore in the parent while the watchdog is still blocked on its
    // lifetime pipe. Closing the pipe then makes the watchdog verify the exact
    // snapshot and retry any part the parent could not restore.
    bool restored = setActive(false, reason);
    // Set ONLY by a read-back check, never by command success; the marker
    // below must not come off on anything weaker (e.g. the watchdog dying
    // between the aliveness check here and a later one).
    bool verifiedRestore = false;
    if (cfg.hardNoSleep && !policyGuardAlive()) {
        // No watchdog left to repair behind us. Judge by what the system
        // actually reads back, not by whether a command reported success —
        // a transient tool outage must not brick future runs. Check first
        // (setActive above already restored on the happy path), and never
        // leave a restore attempt unverified: the final iteration checks
        // rather than fires one more blind restore.
        for (int attempt = 0; attempt < 5; attempt++) {
            if (persistentPolicyMatchesSnapshot()) {
                verifiedRestore = true;
                break;
            }
            if (attempt == 4) break;
            sleep(2);
            (void)restorePersistentPolicySnapshot();
        }
        restored = verifiedRestore;
        if (!restored) {
            warn("could not restore the original policy and no watchdog is "
                 "alive; the values needed are in %s", kPolicyStatePath);
            code = 1;
        }
    }
    if (verifiedRestore && !removePolicyStateMarker()) {
        warn("settings restored, but could not remove %s: %s",
             kPolicyStatePath, strerror(errno));
        if (code == 0) code = 1;
    }
    if (!stopPolicyGuard() && code == 0) code = 1;
    if (gUserActivityID != kIOPMNullAssertionID) {
        IOPMAssertionRelease(gUserActivityID);
        gUserActivityID = kIOPMNullAssertionID;
    }
    if (gEventSource) {
        CFRelease(gEventSource);
        gEventSource = nullptr;
    }
    teardownPowerNotifications();
    exit(code);
}

static void reconcile(const char *trigger);

static void powerCallback(void *refcon, io_service_t service,
                          natural_t messageType, void *messageArgument) {
    (void)refcon; (void)service;
    // Only acknowledge here. Even logging can block on a slow pipe; put it
    // on the main work queue so powerd never waits behind it.
    switch (messageType) {
    case kIOMessageCanSystemSleep:
        if (gActive) {
            IOCancelPowerChange(gRootPort, (long)messageArgument);
            if (gMainQueue) dispatch_async(gMainQueue, ^{
                info("vetoed an idle-sleep attempt; checking sleep protection");
                reconcile("idle-sleep veto");
            });
        } else {
            IOAllowPowerChange(gRootPort, (long)messageArgument);
        }
        break;
    case kIOMessageSystemWillSleep: {
        IOAllowPowerChange(gRootPort, (long)messageArgument);
        bool hardActive = cfg.hardNoSleep && gActive;
        if (gMainQueue) dispatch_async(gMainQueue, ^{
            if (hardActive)
                warn("system sleep became unavoidable despite hard mode; "
                     "hardware safety and system policy still take priority");
            else
                info("system going to sleep; committed sleep cannot be vetoed");
        });
        break;
    }
    case kIOMessageSystemHasPoweredOn:
        if (gMainQueue) dispatch_async(gMainQueue, ^{
            info("system woke; checking sleep and lock settings");
            gForceFullPolicyCheck = true;
            reconcile("wake");
        });
        break;
    default:
        break;
    }
}

static bool wantActiveNow(const char **why) {
    if (cfg.all) {
        *why = "aggressive all-mode";
        return true;
    }
    if (onACPower()) {
        *why = "on AC power";
        return true;
    }
    if (cfg.acOnly) {
        *why = "on battery (--ac-only)";
        return false;
    }
    if (cfg.minBattery > 0 && batteryPercent() < cfg.minBattery) {
        *why = "battery below --min-battery";
        return false;
    }
    *why = "on battery";
    return true;
}

static void reconcile(const char *trigger) {
    if (gDeadline > 0 && monotonicMilliseconds() >= gDeadline)
        shutdownNow("timeout reached", 0);

    if (cfg.hardNoSleep && !policyGuardAlive()) {
        warn("cleanup watchdog exited unexpectedly; terminating rather than "
             "running with persistent settings but no rollback owner");
        shutdownNow("policy watchdog failure", 1);
    }

    if (cfg.all) {
        ConsoleUser now;
        if (!getConsoleIdentity(&now)) {
            // configd/directory hiccups happen; only a sustained absence
            // (logout, login window) ends the session.
            if (++gConsoleUserMisses >= 5) {
                warn("no logged-in console user; restoring the original "
                     "user's policy before terminating");
                shutdownNow("console user signed out", 1);
            }
        } else if (now.uid != gConsoleUser.uid ||
                   now.gid != gConsoleUser.gid ||
                   strcmp(now.name, gConsoleUser.name) != 0) {
            warn("the logged-in console user changed; restoring the original "
                 "user's policy before terminating");
            shutdownNow("console user changed", 1);
        } else {
            gConsoleUserMisses = 0;
        }
    }

    const char *why = "";
    bool wantActive = wantActiveNow(&why);
    bool ok = true;
    if (wantActive != gActive) {
        ok = setActive(wantActive, why);
        if (!ok) warn("could not apply requested state (%s)", why);
    } else if (gActive) {
        if (!assertionAlive(gSystemAssertion.id)) {
            warn("system assertion vanished (%s); re-creating", trigger);
            ok = acquireAssertion(gSystemAssertion) && ok;
        }
        if (cfg.strong && !assertionAlive(gStrongSystemAssertion.id)) {
            warn("strong system assertion vanished (%s); re-creating", trigger);
            ok = acquireAssertion(gStrongSystemAssertion) && ok;
        }

        if (cfg.hardNoSleep) {
            int disabled = kernelSleepDisabled();
            if (disabled == 0) {
                warn("SleepDisabled was cleared externally (%s); re-applying",
                     trigger);
                gHardSleepApplied = false;
                ok = setHardSleepDisabled(true) && ok;
            } else if (disabled < 0) {
                debug("could not inspect kernel SleepDisabled (%s)", trigger);
            } else if (!gHardSleepApplied) {
                ok = setHardSleepDisabled(true) && ok;
            }
        }

        if (cfg.display) {
            if (!assertionAlive(gDisplayAssertion.id)) {
                warn("display assertion vanished (%s); re-creating", trigger);
                ok = acquireAssertion(gDisplayAssertion) && ok;
            }
            declareUserActivity();
        }

        if (cfg.all) {
            // A failure or filesystem event forces one full preference
            // check; otherwise the expensive full check runs every 5th tick.
            bool fullCheck = gForceFullPolicyCheck ||
                             gPolicyFailures > 0 ||
                             (gAggressiveTicks % 5) == 0;
            gForceFullPolicyCheck = false;
            ok = repairAggressiveLockPolicy(trigger, fullCheck) && ok;

            bool locked = screenLocked();
            if (locked && !gLastScreenLocked) {
                warn("the GUI session became locked despite -a; authentication "
                     "is never bypassed, so unlock it manually. Policy "
                     "reconciliation remains active");
            }
            gLastScreenLocked = locked;
        }
    } else if (cfg.hardNoSleep && gHardSleepApplied) {
        // Paused (battery): the persistent gate must not outlive the pause.
        ok = setHardSleepDisabled(false);
    }

    // One strike counter for everything this pass could not put right. A
    // transient powerd/pmset/sysadminctl hiccup is retried on the next tick
    // (a powerd restart makes every assertion call fail for a moment);
    // a persistent one ends the run — with the watchdog restoring — rather
    // than running forever in a state that is not what was asked for.
    if (!ok) {
        gPolicyFailures++;
        warn("check/repair failed (%u/3); retrying on the next tick",
             gPolicyFailures);
        if (gPolicyFailures >= 3)
            shutdownNow("requested state could not be maintained", 1);
    } else {
        gPolicyFailures = 0;
    }
}

static void tick(void) {
    if (gDeadline > 0 && monotonicMilliseconds() >= gDeadline)
        shutdownNow("timeout reached", 0);
    if (cfg.all) gAggressiveTicks++;
    reconcile("periodic check");
    maybeJiggle();
}

static void setupPreferenceWatchers(dispatch_queue_t queue) {
    if (!cfg.all) return;

    std::string paths[2] = {
        std::string(gConsoleUser.home) + "/Library/Preferences",
        std::string(gConsoleUser.home) + "/Library/Preferences/ByHost",
    };
    unsigned long mask = DISPATCH_VNODE_WRITE | DISPATCH_VNODE_DELETE |
                         DISPATCH_VNODE_RENAME | DISPATCH_VNODE_ATTRIB |
                         DISPATCH_VNODE_EXTEND;
    for (int i = 0; i < 2; i++) {
        int fd = open(paths[i].c_str(), O_EVTONLY | O_CLOEXEC);
        if (fd == -1) {
            debug("could not watch %s: %s", paths[i].c_str(), strerror(errno));
            continue;
        }
        dispatch_source_t source = dispatch_source_create(
            DISPATCH_SOURCE_TYPE_VNODE, (uintptr_t)fd, mask, queue);
        if (!source) {
            close(fd);
            continue;
        }
        gPreferenceWatchFDs[i] = fd;
        gPreferenceWatchers[i] = source;
        dispatch_source_set_event_handler(source, ^{
            // Flag only; the 1 Hz tick performs the check. Reconciling per
            // filesystem event would let unrelated preference churn (and our
            // own writes) saturate the queue with subprocess work.
            gForceFullPolicyCheck = true;
        });
        dispatch_resume(source);
    }
}

// ------------------------------------------------------------------ args ---

static void usage(FILE *to) {
    fprintf(to,
        "kafueineto %s - keep your Mac awake\n"
        "\n"
        "Usage: kafueineto [options]\n"
        "\n"
        "With no options, prevents idle system sleep and nudges the mouse after\n"
        "2 minutes of inactivity; the display may still sleep. Ctrl-C stops it.\n"
        "\n"
        "Without sudo (each row adds to the ones above it)\n"
        "  (default)              Prevent idle system sleep.\n"
        "  -d, --display          Also keep the display awake while it is on.\n"
        "  -x, --max              Also hold the stronger system-sleep assertion,\n"
        "                         nudge the mouse, and request input permission:\n"
        "                         everything that works without sudo. Combine\n"
        "                         freely with -n, -A, -b, -t, or -w.\n"
        "\n"
        "With sudo (changes system settings; restored on exit or by a watchdog)\n"
        "  -H, --hard-no-sleep    Set the system-wide sleep-disable setting (pmset\n"
        "                         disablesleep) and hold the strong assertion.\n"
        "                         Add -d or -x for the display and mouse layers.\n"
        "  -a, --all              Everything: -x and -H plus a temporary override\n"
        "                         of automatic screen locking for the logged-in\n"
        "                         user, who types their login password privately\n"
        "                         in the terminal. Cannot combine with -A, -b, -n.\n"
        "\n"
        "When to stop\n"
        "  -t, --timeout DURATION Stop after this duration (cleanup may take longer).\n"
        "  -w, --waitpid PID      Stop when an existing process exits.\n"
        "\n"
        "Power\n"
        "  -A, --ac-only          Pause while on battery; resume on AC power.\n"
        "  -b, --min-battery PCT  Pause below this battery level (1-100).\n"
        "\n"
        "Mouse input\n"
        "  -n, --no-jiggle        Never move the mouse. Sleep prevention still\n"
        "                         works, and no Accessibility permission is needed.\n"
        "  -i, --idle DURATION    Idle time before a nudge (default 120s, min 5s).\n"
        "      --drift            Leave each nudge in place (drifting toward the\n"
        "                         screen center) instead of returning the pointer.\n"
        "      --request-permission\n"
        "                         Ask macOS for the Accessibility permission mouse\n"
        "                         input needs (-x and -a do this automatically).\n"
        "\n"
        "Information\n"
        "      --idle-probe       Print idle, permission, power, and lid status\n"
        "                         without changing anything, then exit.\n"
        "  -v, --verbose          Show every decision.\n"
        "  -q, --quiet            Show only warnings and errors (overrides -v).\n"
        "  -V, --version          Print the version and exit.\n"
        "  -h, --help             Show this help and exit.\n"
        "\n"
        "Durations are seconds, or a number with s, m, h, or d: 90, 45m, 1.5h, 1d.\n"
        "Timeouts run from 1s to 3650d and start after any password prompt. With\n"
        "both --timeout and --waitpid, whichever comes first ends the run.\n"
        "Aliases: --all-rootless = --max; --aggressive = --all;\n"
        "         --resist-all-sleep = --hard-no-sleep.\n"
        "\n"
        "Examples\n"
        "  kafueineto -n -t 45m          Stay awake 45 minutes, never touch the mouse.\n"
        "  kafueineto -x                 Strongest protection available without sudo.\n"
        "  kafueineto -x -A -w 1234      Same, only on AC power, until pid 1234 exits.\n"
        "  sudo kafueineto -H -t 2h      Also set the system sleep-disable switch.\n"
        "  sudo kafueineto -a -t 30m     Also keep the session from auto-locking.\n"
        "\n"
        "Safety and recovery\n"
        "Sudo modes may keep a closed laptop running: keep it ventilated and\n"
        "never put it in a bag while active. With --all, do not leave it\n"
        "unattended. No mode unlocks a locked session or guarantees blocking\n"
        "every kind of sleep; manual locking, managed policy, shutdown, restart,\n"
        "and hardware safety limits are never bypassed.\n"
        "\n"
        "A cleanup watchdog restores the sudo-mode settings after exit or a crash.\n"
        "Until that is verified, the original values stay in\n"
        "/var/db/kafueineto-policy.state. If the file remains, read it with sudo,\n"
        "restore the listed values, then remove it; sudo modes refuse to start\n"
        "while it exists.\n"
        "\n"
        "Exit codes: 0 = normal stop; 1 = runtime or cleanup error; 2 = bad options.\n",
        kVersion);
}

static double parseDuration(const char *s) {
    if (!s) return -1;
    const char *start = s;
    while (std::isspace((unsigned char)*start)) ++start;
    if (*start == '+') ++start;
    // Accept decimal durations, not C hexadecimal numbers or negatives.
    if (*start == '-' || (start[0] == '0' &&
        (start[1] == 'x' || start[1] == 'X'))) return -1;
    char *end = nullptr;
    errno = 0;
    double v = strtod(s, &end);
    if (errno != 0 || end == s || !std::isfinite(v) || v < 0) return -1;
    switch (*end) {
    case '\0':           break;
    case 's': case 'S':  break;
    case 'm': case 'M':  v *= 60; break;
    case 'h': case 'H':  v *= 3600; break;
    case 'd': case 'D':  v *= 86400; break;
    default: return -1;
    }
    if (*end != '\0' && end[1] != '\0') return -1;
    if (!std::isfinite(v) || v > 10.0 * 365 * 86400) return -1;
    return v;
}

static bool parseInteger(const char *s, long minimum, long maximum, long *out) {
    if (!s || !out) return false;
    char *end = nullptr;
    errno = 0;
    long value = strtol(s, &end, 10);
    if (errno != 0 || end == s || *end != '\0' ||
        value < minimum || value > maximum) return false;
    *out = value;
    return true;
}

static void parseArgs(int argc, char **argv) {
    enum { OptRequestPerm = 1000, OptIdleProbe, OptDrift };
    static const struct option longOpts[] = {
        {"all",                no_argument,       nullptr, 'a'},
        {"aggressive",         no_argument,       nullptr, 'a'},
        {"max",                no_argument,       nullptr, 'x'},
        {"all-rootless",       no_argument,       nullptr, 'x'},
        {"display",            no_argument,       nullptr, 'd'},
        {"idle",               required_argument, nullptr, 'i'},
        {"no-jiggle",          no_argument,       nullptr, 'n'},
        {"drift",              no_argument,       nullptr, OptDrift},
        {"hard-no-sleep",      no_argument,       nullptr, 'H'},
        {"resist-all-sleep",   no_argument,       nullptr, 'H'},
        {"ac-only",            no_argument,       nullptr, 'A'},
        {"min-battery",        required_argument, nullptr, 'b'},
        {"timeout",            required_argument, nullptr, 't'},
        {"waitpid",            required_argument, nullptr, 'w'},
        {"idle-probe",         no_argument,       nullptr, OptIdleProbe},
        {"request-permission", no_argument,       nullptr, OptRequestPerm},
        {"verbose",            no_argument,       nullptr, 'v'},
        {"quiet",              no_argument,       nullptr, 'q'},
        {"version",            no_argument,       nullptr, 'V'},
        {"help",               no_argument,       nullptr, 'h'},
        {nullptr, 0, nullptr, 0},
    };

    int c;
    while ((c = getopt_long(argc, argv, "axdnHi:Ab:t:w:vqVh", longOpts,
                            nullptr)) != -1) {
        switch (c) {
        case 'a': cfg.all = true; break;
        case 'x': cfg.max = true; break;
        case 'd': cfg.display = true; break;
        case 'A': cfg.acOnly = true; break;
        case 'b': {
            long pct = 0;
            if (!parseInteger(optarg, 1, 100, &pct)) {
                fprintf(stderr,
                        "kafueineto: --min-battery needs a whole number from 1 to 100\n");
                exit(2);
            }
            cfg.minBattery = (int)pct;
            break;
        }
        case OptIdleProbe: cfg.idleProbe = true; break;
        case 'i':
            cfg.idleThreshold = parseDuration(optarg);
            if (cfg.idleThreshold < 5) {
                fprintf(stderr, "kafueineto: --idle needs a duration from 5s to "
                                "3650d (for example, 120 or 2m)\n");
                exit(2);
            }
            break;
        case 'n':
            cfg.jiggle = false;
            cfg.noJiggleExplicit = true;
            break;
        case OptDrift: cfg.drift = true; break;
        case 'H': cfg.hardNoSleep = true; break;
        case 't':
            cfg.timeout = parseDuration(optarg);
            if (cfg.timeout < 1) {
                fprintf(stderr, "kafueineto: --timeout needs a duration from 1s "
                                "to 3650d (for example, 45m or 2h); got '%s'\n",
                        optarg);
                exit(2);
            }
            break;
        case 'w': {
            long pid = 0;
            if (!parseInteger(optarg, 1, std::numeric_limits<pid_t>::max(), &pid)) {
                fprintf(stderr, "kafueineto: --waitpid needs a valid positive "
                                "process ID; got '%s'\n", optarg);
                exit(2);
            }
            if (kill((pid_t)pid, 0) == -1 && errno != EPERM) {
                fprintf(stderr, "kafueineto: cannot watch process %ld: %s\n",
                        pid, strerror(errno));
                exit(2);
            }
            cfg.waitPid = (pid_t)pid;
            break;
        }
        case OptRequestPerm: cfg.requestPerm = true; break;
        case 'v': cfg.verbose++; break;
        case 'q': cfg.quiet = true; break;
        case 'V': printf("kafueineto %s\n", kVersion); exit(0);
        case 'h': usage(stdout); exit(0);
        default:
            fprintf(stderr, "Try 'kafueineto --help' for options and examples.\n");
            exit(2);
        }
    }

    if (optind < argc) {
        fprintf(stderr, "kafueineto: unexpected argument '%s'\n", argv[optind]);
        fprintf(stderr, "Try 'kafueineto --help' for options and examples.\n");
        exit(2);
    }

    // Presets resolve top-down: -a is -x plus the root-only layers, and -x is
    // every layer that needs no privilege.
    if (cfg.all) {
        if (cfg.acOnly || cfg.minBattery > 0 || cfg.noJiggleExplicit) {
            fprintf(stderr,
                    "kafueineto: -a/--all cannot be combined with --ac-only, "
                    "--min-battery, or --no-jiggle (use -x for the sudo-free "
                    "layers with those options)\n");
            exit(2);
        }
        cfg.max = true;
        cfg.hardNoSleep = true;
        cfg.jiggle = true;
    }
    if (cfg.max) {
        // An explicit --no-jiggle still wins: a preset plus an opt-out is
        // exactly what the user asked for, and asking for input permission
        // would then be pointless.
        cfg.display = true;
        cfg.strong = true;
        if (cfg.jiggle) cfg.requestPerm = true;
    }
    // Hard mode has always held the strong assertion next to SleepDisabled.
    if (cfg.hardNoSleep) cfg.strong = true;

    if (cfg.drift && !cfg.jiggle) {
        fprintf(stderr, "kafueineto: --drift requires mouse input; "
                        "remove --no-jiggle or --drift\n");
        exit(2);
    }
    if (cfg.acOnly && cfg.minBattery > 0)
        fprintf(stderr, "kafueineto: note: --min-battery is redundant with "
                        "--ac-only, which always pauses on battery\n");

    if (cfg.requestPerm && !cfg.jiggle)
        fprintf(stderr,
                "kafueineto: note: --request-permission does nothing with "
                "--no-jiggle\n");
}

// ------------------------------------------------------------------ main ---

int main(int argc, char **argv) {
    parseArgs(argc, argv);
    if (cfg.idleProbe) return idleProbe();

    // A helper child that dies before consuming its pty/pipe input must
    // surface as a write error, never kill this process.
    signal(SIGPIPE, SIG_IGN);

    // Snapshot and arm rollback before changing any persistent setting and
    // before dispatch/ApplicationServices can create helper threads.
    // startPolicyGuard bases the -t deadline itself, after its interactive
    // password prompt; set it here only for the guardless modes.
    if (!startPolicyGuard()) return 1;
    if (cfg.timeout > 0 && gDeadline == 0)
        gDeadline = monotonicMilliseconds() + durationMilliseconds(cfg.timeout);

    dispatch_queue_t q = dispatch_queue_create(
        "kafueineto.main", dispatch_queue_attr_make_with_qos_class(
                             DISPATCH_QUEUE_SERIAL, QOS_CLASS_UTILITY, 0));
    if (!q) shutdownNow("could not create the main work queue", 1);
    // Finish startup before any notification can run a concurrent reconcile.
    dispatch_suspend(q);
    gMainQueue = q;

    if (cfg.jiggle) {
        gEventSource = CGEventSourceCreate(kCGEventSourceStateHIDSystemState);
        if (gEventSource)
            CGEventSourceSetLocalEventsSuppressionInterval(gEventSource, 0.0);

        CFTypeRef axKeys[] = {kAXTrustedCheckOptionPrompt};
        CFTypeRef axVals[] = {kCFBooleanFalse};
        CFDictionaryRef axOpts = CFDictionaryCreate(
            kCFAllocatorDefault, axKeys, axVals, 1,
            &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);
        if (axOpts) {
            AXIsProcessTrustedWithOptions(axOpts);
            CFRelease(axOpts);
        }
        if (cfg.requestPerm && !canPostEvents()) {
            info("requesting Accessibility input-event permission");
            CGRequestPostEventAccess();
        }
    }

    const char *why = "";
    bool want = wantActiveNow(&why);
    if (!setActive(want, "startup")) {
        warn("could not activate the requested policy; restoring snapshot");
        (void)restorePersistentPolicySnapshot();
        if (gEventSource) {
            CFRelease(gEventSource);
            gEventSource = nullptr;
        }
        // Unconfirmed restoration already warns inside, and this path exits
        // 1 regardless; the watchdog keeps the marker until it verifies.
        (void)stopPolicyGuard();
        return 1;
    }
    if (!gActive) info("idling until power conditions allow (%s)", why);
    gLastScreenLocked = screenLocked();

    gRootPort = IORegisterForSystemPower(nullptr, &gNotifyPort, powerCallback,
                                         &gNotifier);
    if (gRootPort == MACH_PORT_NULL) {
        warn("IORegisterForSystemPower failed; wake re-assert and idle-sleep "
             "veto are unavailable");
    } else {
        // Dedicated queue: the sleep-veto acknowledgement must never wait
        // behind subprocess-heavy policy work on the main queue.
        gPowerQueue = dispatch_queue_create(
            "kafueineto.power", dispatch_queue_attr_make_with_qos_class(
                                    DISPATCH_QUEUE_SERIAL,
                                    QOS_CLASS_USER_INITIATED, 0));
        if (!gPowerQueue) shutdownNow("could not create the power event queue", 1);
        IONotificationPortSetDispatchQueue(gNotifyPort, gPowerQueue);
    }

    int resyncToken = 0;
    uint32_t ns = notify_register_dispatch(
        "com.apple.system.powermanagement.assertionresync", &resyncToken, q,
        ^(int) {
            warn("powerd restarted; re-establishing all assertions");
            gSystemAssertion.id = kIOPMNullAssertionID;
            gStrongSystemAssertion.id = kIOPMNullAssertionID;
            gDisplayAssertion.id = kIOPMNullAssertionID;
            gUserActivityID = kIOPMNullAssertionID;
            reconcile("powerd restart");
        });
    if (ns != NOTIFY_STATUS_OK)
        debug("assertionresync notify unavailable (status %u); timer covers it",
              ns);

    int psToken = 0;
    ns = notify_register_dispatch(kIOPSNotifyPowerSource, &psToken, q,
                                  ^(int) { reconcile("power source change"); });
    if (ns != NOTIFY_STATUS_OK)
        debug("power-source notify unavailable (status %u)", ns);

    // Event-driven detection for the preference-backed layers. The modern
    // keybag-backed Screen Lock setting is additionally polled every second.
    setupPreferenceWatchers(q);

    signal(SIGINT, SIG_IGN);
    signal(SIGTERM, SIG_IGN);
    signal(SIGHUP, SIG_IGN);
    for (int sig : {SIGINT, SIGTERM, SIGHUP}) {
        dispatch_source_t source = dispatch_source_create(
            DISPATCH_SOURCE_TYPE_SIGNAL, (uintptr_t)sig, 0, q);
        if (!source) shutdownNow("could not monitor termination signals", 1);
        dispatch_source_set_event_handler(source, ^{
            shutdownNow(sig == SIGINT   ? "interrupted"
                        : sig == SIGHUP ? "hangup"
                                        : "terminated",
                        0);
        });
        dispatch_resume(source);
    }

    double tickSec;
    if (cfg.all) {
        tickSec = 1.0;
    } else {
        tickSec = cfg.idleThreshold / 2.0;
        if (tickSec > 30.0) tickSec = 30.0;
        if (tickSec < 5.0) tickSec = 5.0;
    }
    uint64_t tickNs = (uint64_t)(tickSec * NSEC_PER_SEC);
    gTimer = dispatch_source_create(DISPATCH_SOURCE_TYPE_TIMER, 0, 0, q);
    if (!gTimer) shutdownNow("could not create the periodic timer", 1);
    dispatch_source_set_timer(gTimer,
                              dispatch_time(DISPATCH_TIME_NOW, (int64_t)tickNs),
                              tickNs, cfg.all ? 0 : tickNs / 10);
    dispatch_source_set_event_handler(gTimer, ^{ tick(); });
    dispatch_resume(gTimer);

    if (cfg.timeout > 0) {
        // Base this on gDeadline, which startPolicyGuard may have rebased
        // after its password prompt, so all four -t mechanisms agree.
        double remaining = (gDeadline - monotonicMilliseconds()) / 1000.0;
        if (remaining < 0) remaining = 0;
        dispatch_after(dispatch_time(DISPATCH_TIME_NOW,
                                      (int64_t)(remaining * NSEC_PER_SEC)),
                       q, ^{ shutdownNow("timeout reached", 0); });
    }

    if (cfg.waitPid > 0) {
        dispatch_source_t ps = dispatch_source_create(
            DISPATCH_SOURCE_TYPE_PROC, (uintptr_t)cfg.waitPid,
            DISPATCH_PROC_EXIT, q);
        if (!ps) shutdownNow("could not monitor the requested process", 1);
        dispatch_source_set_event_handler(ps, ^{
            shutdownNow("watched process exited", 0);
        });
        dispatch_resume(ps);
        if (kill(cfg.waitPid, 0) == -1 && errno == ESRCH)
            shutdownNow("watched process already exited", 0);
    }

    info("up: pid %d | %s%s%s%s | jiggle %s "
         "(idle > %.0fs, tick %.0fs)%s%s",
         getpid(),
         gActive ? "system sleep blocked" : "sleep blocking paused",
         gActive && cfg.hardNoSleep ? " | hard no-sleep requested"
         : gActive && cfg.strong    ? " | strong assertion held" : "",
         gActive && cfg.display ? " | display sleep blocked" : "",
         gActive && cfg.all ? " | automatic Screen Lock disabled" : "",
         cfg.jiggle ? (canPostEvents() ? "armed" : "blocked (no permission)")
                    : "off",
         cfg.idleThreshold, tickSec,
         cfg.acOnly ? " | AC-only" : "",
         cfg.timeout > 0 ? " | timed" : "");

    dispatch_resume(q);
    dispatch_main();
    return 0;  // dispatch_main() does not return; keeps test builds warning-free.
}
