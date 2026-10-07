// Test harness: compiles the real kafueineto.cpp with main renamed, then
// drives its parsers and subprocess plumbing with real-world inputs.
// Build and run with `make test`. Safe to run unprivileged: system probes
// are read-only, and writes go only to the throwaway com.kafueineto.test
// defaults domain and private temporary directories under /tmp.
#define main kafueineto_main
#include "kafueineto.cpp"
#undef main

static int gFailures = 0;
static int gChecks = 0;

#define CHECK(cond, ...) do { \
    gChecks++; \
    if (!(cond)) { \
        gFailures++; \
        printf("FAIL %s:%d  %s  — ", __FILE__, __LINE__, #cond); \
        printf(__VA_ARGS__); \
        printf("\n"); \
    } \
} while (0)

static ConsoleUser currentUser(void) {
    ConsoleUser u;
    struct passwd *pw = getpwuid(getuid());
    if (!pw) return u;
    u.valid = true;
    u.uid = getuid();
    u.gid = getgid();
    strlcpy(u.name, pw->pw_name, sizeof u.name);
    strlcpy(u.home, pw->pw_dir, sizeof u.home);
    int n = (int)(sizeof u.groups / sizeof u.groups[0]);
#ifdef __APPLE__
    int *groups = (int *)(void *)u.groups;
#else
    gid_t *groups = u.groups;
#endif
    if (getgrouplist(pw->pw_name, (int)u.gid, groups, &n) != -1)
        u.groupCount = n;
    else
        u.groupCount = 1, u.groups[0] = u.gid;
    return u;
}

static void testParseLockMode(void) {
    LockMode m;
    // Captured sample supplied with the original suite (macOS 27.0):
    CHECK(parseLockMode("2026-07-31 09:53:19.273 sysadminctl[7812:9566035] "
                        "screenLock delay is immediate", &m) &&
          m.kind == LockKind::Immediate, "real sysadminctl output");
    CHECK(parseLockMode("screenLock delay is off", &m) &&
          m.kind == LockKind::Off, "delay off");
    CHECK(parseLockMode("sysadminctl[1:2] screenLock delay is 300 seconds",
                        &m) && m.kind == LockKind::Seconds && m.seconds == 300,
          "delay 300 got kind=%d s=%d", (int)m.kind, m.seconds);
    CHECK(parseLockMode("Screen lock is off", &m) && m.kind == LockKind::Off,
          "classic off");
    CHECK(parseLockMode("Screen lock is immediate", &m) &&
          m.kind == LockKind::Immediate, "classic immediate");
    CHECK(parseLockMode("screenLock is 45 seconds", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 45, "classic 45");
    CHECK(parseLockMode("screenLock delay is disabled", &m) &&
          m.kind == LockKind::Off, "disabled wording");
    CHECK(parseLockMode("screenLock delay is 0 seconds", &m) &&
          m.kind == LockKind::Immediate, "0s == immediate");
    CHECK(!parseLockMode("no lock information here", &m), "garbage rejected");
    CHECK(!parseLockMode("", &m), "empty rejected");
    // Regression: a unit we don't understand must fail the parse, not be
    // read as seconds — "5 minutes" as Seconds(5) would restore a 60x
    // tighter policy while the verify-by-re-read happily agrees.
    CHECK(!parseLockMode("screenLock delay is 5 minutes", &m),
          "unknown unit rejected (would be a silent 60x downgrade)");
    CHECK(!parseLockMode("screenLock delay is 5 hours", &m),
          "hours rejected");
    CHECK(parseLockMode("screenLock delay is 300 second", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 300, "singular second");
    CHECK(parseLockMode("screenLock delay is 300", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 300, "bare number");
    // Regression: the digit scan skipped a leading minus, reading "-5" as
    // Seconds(5) and making the negative-value guard dead code.
    CHECK(!parseLockMode("screenLock delay is -5 seconds", &m),
          "negative delay rejected");
    // The whole seconds family must parse; refusing "secs" refuses to arm.
    CHECK(parseLockMode("screenLock delay is 300 secs", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 300, "secs accepted");
    CHECK(parseLockMode("screenLock delay is 300 sec", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 300, "sec accepted");
    CHECK(parseLockMode("screenLock delay is 300 s", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 300, "bare s accepted");
    CHECK(!parseLockMode("screenLock delay is 300 sols", &m),
          "unknown s-word still rejected");
}

static void testParseSleepDisabledOutput(void) {
    int v = -1;
    // Real `pmset -g` shape on this machine: leading space, tab separators.
    CHECK(parseSleepDisabledOutput(
              "System-wide power settings:\n SleepDisabled\t\t0\n"
              "Currently in use:\n standby\t\t1\n", &v) && v == 0,
          "real pmset shape (got %d)", v);
    CHECK(parseSleepDisabledOutput(" SleepDisabled\t\t1\n", &v) && v == 1,
          "value 1");
    // Regression: an unanchored substring match let any later
    // "...SleepDisabled" row shadow the real one under last-wins.
    CHECK(parseSleepDisabledOutput(
              " SleepDisabled\t1\n kIOPMSleepDisabled\t0\n", &v) && v == 1,
          "suffix-named later row ignored (got %d)", v);
    CHECK(!parseSleepDisabledOutput(" kIOPMSleepDisabled\t1\n", &v),
          "suffix-named row alone is not a match");
    CHECK(parseSleepDisabledOutput(
              "SleepDisabled 0\nSleepDisabled 1\n", &v) && v == 1,
          "last anchored row wins (pmset semantics)");
    CHECK(!parseSleepDisabledOutput("SleepDisabled\n1\n", &v),
          "number on the next line rejected");
    CHECK(!parseSleepDisabledOutput("no such row\n", &v), "absent row");
    CHECK(!parseSleepDisabledOutput("", &v), "empty");
}

static void testParseDuration(void) {
    CHECK(parseDuration("90") == 90.0, "plain seconds");
    CHECK(parseDuration("45m") == 2700.0, "minutes");
    CHECK(parseDuration("2h") == 7200.0, "hours");
    CHECK(parseDuration("1.5h") == 5400.0, "fractional hours");
    CHECK(parseDuration("1d") == 86400.0, "days");
    CHECK(parseDuration("0") == 0.0, "zero parses (caller rejects)");
    CHECK(parseDuration("") == -1, "empty");
    CHECK(parseDuration("x") == -1, "junk");
    CHECK(parseDuration("5x") == -1, "bad suffix");
    CHECK(parseDuration("5mm") == -1, "trailing junk");
    CHECK(parseDuration("-3") == -1, "negative");
    CHECK(parseDuration("1e400") == -1, "infinite");
    CHECK(parseDuration("99999d") == -1, "over cap");
    CHECK(parseDuration("30s") == 30.0, "explicit seconds suffix");
    // Regression: the 10-year cap must catch bare-second values too, or a
    // huge -t overflows time_t and disarms every timeout mechanism.
    CHECK(parseDuration("315360001") == -1, "bare seconds over cap");
    CHECK(parseDuration("1e19") == -1, "time_t overflow rejected");

    char text[48];
    CHECK(!strcmp(formatDuration(0, text, sizeof text), "0s"), "format zero");
    CHECK(!strcmp(formatDuration(59.4, text, sizeof text), "59s"),
          "format rounds to whole seconds");
    CHECK(!strcmp(formatDuration(2700, text, sizeof text), "45m 0s"),
          "format minutes");
    CHECK(!strcmp(formatDuration(5400, text, sizeof text), "1h 30m 0s"),
          "format hours");
    CHECK(!strcmp(formatDuration(90000, text, sizeof text), "1d 1h 0m"),
          "format days");
    CHECK(!strcmp(formatDuration(-5, text, sizeof text), "0s"),
          "format clamps negative");
}

static void testParseNumericPreference(void) {
    double v = 0;
    CHECK(parseNumericPreference("1", &v) && v == 1.0, "int 1");
    CHECK(parseNumericPreference("0", &v) && v == 0.0, "int 0");
    CHECK(parseNumericPreference("1800\n", &v) && v == 1800.0, "trailing nl");
    CHECK(parseNumericPreference("  42  ", &v) && v == 42.0, "spaces");
    CHECK(parseNumericPreference("true", &v) && v == 1.0, "true");
    CHECK(parseNumericPreference("NO", &v) && v == 0.0, "NO");
    CHECK(parseNumericPreference("0.5", &v) && v == 0.5, "float");
    CHECK(parseNumericPreference("2147483647", &v) && v == 2147483647.0,
          "INT_MAX");
    CHECK(!parseNumericPreference("abc", &v), "junk rejected");
    CHECK(!parseNumericPreference("1 2", &v), "two numbers rejected");
    CHECK(!parseNumericPreference("", &v), "empty rejected");
    CHECK(!parseNumericPreference("inf", &v), "inf rejected");
    // Regression: past 2^53 a double cannot round-trip the integer, so the
    // snapshot would not restore exactly — refuse it instead.
    CHECK(!parseNumericPreference("9007199254740993", &v),
          "2^53+1 rejected (rounds to 2^53, would not restore exactly)");
    CHECK(parseNumericPreference("9007199254740992", &v) &&
          v == 9007199254740992.0, "2^53 accepted exactly");
    CHECK(!parseNumericPreference("99999999999999999999999", &v),
          "beyond long long rejected");
    // Regression: strtod("LLONG_MAX") rounds up to 2^63, and the cast back
    // was UB that saturates on arm64 into a false "round-trips exactly".
    CHECK(!parseNumericPreference("9223372036854775807", &v),
          "LLONG_MAX rejected (cast-back UB falsely passed it)");
    CHECK(!parseNumericPreference("-9223372036854775808", &v),
          "LLONG_MIN rejected");
    // Regression: strtod eats C99 hex, and the integer classifier skipped
    // its round-trip check for it.
    CHECK(!parseNumericPreference("0x10", &v), "hex rejected");
    CHECK(!parseNumericPreference("-0X10", &v), "signed hex rejected");
    CHECK(parseNumericPreference("-42", &v) && v == -42.0, "negative int");
    CHECK(parseNumericPreference("2147483647", &v) && v == 2147483647.0,
          "INT_MAX round-trips (the askForPasswordDelay value we write)");
    CHECK(prefValuesEqual(PrefValueType::Integer, 5, 5), "int eq");
    CHECK(!prefValuesEqual(PrefValueType::Integer, 5, 6), "int neq");
    CHECK(prefValuesEqual(PrefValueType::Float, 0.5, 0.5000001), "float tol");
    CHECK(!prefValuesEqual(PrefValueType::Float, 0.5, 0.6), "float neq");
}

static void testCollectChild(void) {
    ConsoleUser u = currentUser();
    CHECK(u.valid, "current user resolved");

    CommandResult r = runCapturedAsUser(u, {"/bin/echo", "hello"});
    CHECK(r.launched && !r.timedOut && r.exitCode == 0 &&
          r.output.find("hello") != std::string::npos,
          "echo: launched=%d timedOut=%d exit=%d out='%s'",
          r.launched, r.timedOut, r.exitCode, r.output.c_str());

    r = runCapturedAsUser(u, {"/bin/sh", "-c", "exit 7"});
    CHECK(r.exitCode == 7, "exit code propagation, got %d", r.exitCode);

    r = runCapturedAsUser(u, {"/nonexistent-binary"});
    CHECK(r.launched && r.exitCode == 127, "exec failure -> 127, got %d",
          r.exitCode);

    // Regression: a grandchild inheriting stdout must not hang collectChild
    // (previously an unbounded 1ms-spin until the grandchild exited).
    int64_t t0 = monotonicMilliseconds();
    r = runCapturedAsUser(u, {"/bin/sh", "-c",
                              "echo started; sleep 15 & exit 0"}, 10000);
    int64_t elapsed = monotonicMilliseconds() - t0;
    CHECK(r.launched && !r.timedOut && r.exitCode == 0 &&
          r.output.find("started") != std::string::npos,
          "grandchild: timedOut=%d exit=%d out='%s'",
          r.timedOut, r.exitCode, r.output.c_str());
    CHECK(elapsed < 6000, "grandchild drain bounded, took %lld ms",
          (long long)elapsed);

    // Timeout kill path.
    t0 = monotonicMilliseconds();
    r = runCapturedAsUser(u, {"/bin/sh", "-c", "sleep 20"}, 1500);
    elapsed = monotonicMilliseconds() - t0;
    CHECK(r.timedOut, "timeout flagged");
    CHECK(elapsed < 6000, "timeout bounded, took %lld ms", (long long)elapsed);

    // Output cap: 200k of output must not overflow the 64k cap or hang.
    r = runCapturedAsUser(u, {"/bin/sh", "-c",
                              "/usr/bin/head -c 200000 /dev/zero | "
                              "/usr/bin/tr '\\0' 'x'"});
    CHECK(r.exitCode == 0 && r.output.size() == 65536,
          "output capped at 64k, got %zu", r.output.size());

    // Regression: a child that closes stdout/stderr and lingers used to make
    // the reader spin at 100% CPU until the child exited.
    struct rusage ru0 = {}, ru1 = {};
    getrusage(RUSAGE_SELF, &ru0);
    t0 = monotonicMilliseconds();
    r = runCapturedAsUser(u, {"/bin/sh", "-c", "exec 1>&- 2>&-; sleep 3"});
    elapsed = monotonicMilliseconds() - t0;
    getrusage(RUSAGE_SELF, &ru1);
    double cpuSec =
        (ru1.ru_utime.tv_sec - ru0.ru_utime.tv_sec) +
        (ru1.ru_stime.tv_sec - ru0.ru_stime.tv_sec) +
        (ru1.ru_utime.tv_usec - ru0.ru_utime.tv_usec) / 1e6 +
        (ru1.ru_stime.tv_usec - ru0.ru_stime.tv_usec) / 1e6;
    CHECK(r.exitCode == 0 && elapsed >= 2500,
          "early-close child waited for, exit=%d elapsed=%lld",
          r.exitCode, (long long)elapsed);
    CHECK(cpuSec < 0.5, "no busy-spin while waiting (used %.2fs CPU)",
          cpuSec);
}

static void testDefaultsPipeline(void) {
    gConsoleUser = currentUser();
    std::string domain = "com.kafueineto.test." + std::to_string(getpid());
    IntPrefSnapshot intPref  = {domain.c_str(), "intKey",  false};
    IntPrefSnapshot boolPref = {domain.c_str(), "boolKey", false};
    IntPrefSnapshot fltPref  = {domain.c_str(), "fltKey",  false};
    IntPrefSnapshot ghost    = {domain.c_str(), "noSuchKey", false};
    IntPrefSnapshot hostPref = {domain.c_str(), "hostKey", true};

    // Clean slate.
    runCapturedAsUser(gConsoleUser,
                      {"/usr/bin/defaults", "delete", domain});

    // Missing key/domain must read as valid-but-absent (new error wording).
    CHECK(readPreference(&ghost, false) && ghost.valid && !ghost.existed,
          "missing key detected via current defaults error message");

    CHECK(writePreference(intPref, 42, PrefValueType::Integer), "write int");
    CHECK(writePreference(boolPref, 1, PrefValueType::Boolean), "write bool");
    CHECK(writePreference(fltPref, 0.5, PrefValueType::Float), "write float");
    CHECK(writePreference(hostPref, 7, PrefValueType::Integer),
          "write currentHost int");

    IntPrefSnapshot readBack = intPref;
    CHECK(readPreference(&readBack, true) && readBack.existed &&
          readBack.value == 42 && readBack.type == PrefValueType::Integer,
          "read-type int, got type=%d v=%g", (int)readBack.type,
          readBack.value);
    readBack = boolPref;
    CHECK(readPreference(&readBack, true) && readBack.existed &&
          readBack.value == 1 && readBack.type == PrefValueType::Boolean,
          "read-type bool, got type=%d v=%g", (int)readBack.type,
          readBack.value);
    readBack = fltPref;
    CHECK(readPreference(&readBack, true) && readBack.existed &&
          prefValuesEqual(PrefValueType::Float, readBack.value, 0.5) &&
          readBack.type == PrefValueType::Float,
          "read-type float, got type=%d v=%g", (int)readBack.type,
          readBack.value);

    // Snapshot -> clobber -> restore-from-snapshot round trip (the -a flow).
    IntPrefSnapshot snap = fltPref;
    CHECK(readPreference(&snap, true) && snap.valid && snap.existed,
          "snapshot float");
    CHECK(writePreference(fltPref, 9999, PrefValueType::Integer),
          "clobber with aggressive int");
    CHECK(writePreference(snap, snap.value, snap.type), "restore snapshot");
    readBack = fltPref;
    CHECK(readPreference(&readBack, true) &&
          readBack.type == PrefValueType::Float &&
          prefValuesEqual(PrefValueType::Float, readBack.value, 0.5),
          "restored to float 0.5, got type=%d v=%g", (int)readBack.type,
          readBack.value);

    // Snapshot of an absent key restores by deletion.
    IntPrefSnapshot ghostSnap = ghost;
    CHECK(readPreference(&ghostSnap, true) && !ghostSnap.existed,
          "ghost snapshot absent");
    CHECK(writePreference(ghost, 1, PrefValueType::Integer), "create ghost");
    CHECK(deletePreference(ghostSnap), "delete restores absence");
    readBack = ghost;
    CHECK(readPreference(&readBack, false) && !readBack.existed,
          "ghost absent again");

    // Regression: an EXISTING but unreadable plist must never be mistaken
    // for an absent one — restore would delete the user's live setting.
    // com.apple.screensaver ByHost really holds idleTime on this machine.
    IntPrefSnapshot realPref = {"com.apple.screensaver", "idleTime", true};
    IntPrefSnapshot readReal = realPref;
    bool haveReal = readPreference(&readReal, true) && readReal.existed;
    // This key is not present on every Mac. Synthetic-home tests below
    // always cover existence; do not require the developer's personal setup.
    if (haveReal)
        CHECK(!preferenceDomainFileMissing(realPref),
              "existing ByHost domain not reported missing");
    IntPrefSnapshot fakeDomain = {"com.kafueineto.nosuchdomain", "k", false};
    CHECK(preferenceDomainFileMissing(fakeDomain),
          "truly absent domain reported missing");
    IntPrefSnapshot fakeHost = {"com.kafueineto.nosuchdomain", "k", true};
    CHECK(preferenceDomainFileMissing(fakeHost),
          "truly absent ByHost domain reported missing");

    // Cleanup.
    runCapturedAsUser(gConsoleUser,
                      {"/usr/bin/defaults", "delete", domain});
    runCapturedAsUser(gConsoleUser,
                      {"/usr/bin/defaults", "-currentHost", "delete",
                       domain});
}

// preferenceDomainFileMissing against a synthetic home directory: the ByHost
// scan must match stored names case-insensitively (APFS folds case; Apple
// ships mixed-case ByHost names) and must respect the domain boundary dot.
static void testDomainFileScan(void) {
    ConsoleUser saved = gConsoleUser;
    gConsoleUser = currentUser();
    char temp[] = "/tmp/kafueineto-domscan.XXXXXX";
    char *dir = mkdtemp(temp);
    CHECK(dir != nullptr, "create isolated synthetic home");
    if (!dir) return;
    std::string home = dir;
    std::string prefs = home + "/Library/Preferences";
    std::string byhost = prefs + "/ByHost";
    mkdir((home + "/Library").c_str(), 0700);
    mkdir(prefs.c_str(), 0700);
    mkdir(byhost.c_str(), 0700);
    std::string plist = byhost + "/com.KAFUEINETO.CaseTest.0000-1111.plist";
    std::string any = prefs + "/com.kafueineto.anyhost.plist";
    FILE *f = fopen(plist.c_str(), "w");
    CHECK(f != nullptr, "create ByHost plist");
    if (f) fclose(f);
    f = fopen(any.c_str(), "w");
    CHECK(f != nullptr, "create anyHost plist");
    if (f) fclose(f);

    strlcpy(gConsoleUser.home, home.c_str(), sizeof gConsoleUser.home);
    IntPrefSnapshot caseHost = {"com.kafueineto.casetest", "k", true};
    CHECK(!preferenceDomainFileMissing(caseHost),
          "case-mismatched live ByHost plist is found (not 'absent')");
    IntPrefSnapshot ghostHost = {"com.kafueineto.absent", "k", true};
    CHECK(preferenceDomainFileMissing(ghostHost),
          "absent ByHost domain reported missing");
    IntPrefSnapshot anyHost = {"com.kafueineto.anyhost", "k", false};
    CHECK(!preferenceDomainFileMissing(anyHost), "anyHost plist found");
    IntPrefSnapshot anyGhost = {"com.kafueineto.absent", "k", false};
    CHECK(preferenceDomainFileMissing(anyGhost),
          "absent anyHost domain reported missing");
    // "com.kafueineto.casetes" is a prefix of the stored name but a
    // different domain; the boundary dot must reject it.
    IntPrefSnapshot prefixHost = {"com.kafueineto.casetes", "k", true};
    CHECK(preferenceDomainFileMissing(prefixHost),
          "prefix of a stored name is not a match");
    // A dangling symlink is evidence of an existing domain, not absence.
    std::string dangling = prefs + "/com.kafueineto.dangling.plist";
    CHECK(symlink("missing-target", dangling.c_str()) == 0, "create dangling link");
    IntPrefSnapshot danglingPref = {"com.kafueineto.dangling", "k", false};
    CHECK(!preferenceDomainFileMissing(danglingPref),
          "dangling preference symlink is not treated as absent");
    unlink(dangling.c_str());
    gConsoleUser = saved;

    unlink(plist.c_str());
    unlink(any.c_str());
    rmdir(byhost.c_str());
    rmdir(prefs.c_str());
    rmdir((home + "/Library").c_str());
    rmdir(home.c_str());
}

static void testSystemReadOnly(void) {
    // Full pipeline against the real sysadminctl status (read-only).
    gConsoleUser = currentUser();
    LockMode m;
    CHECK(readScreenLockMode(&m), "readScreenLockMode against real system");
    CHECK(m.kind != LockKind::Invalid, "parsed a real lock mode (kind=%d)",
          (int)m.kind);

    int sleepDisabled = -1;
    CHECK(readPmsetSleepDisabled(&sleepDisabled) &&
          (sleepDisabled == 0 || sleepDisabled == 1),
          "readPmsetSleepDisabled, got %d", sleepDisabled);
}

// Shared by the native suite and tests/run_portable.py. No macOS policy is
// changed by these tests; marker files live only in a private temporary folder.
static void testParserHardening(void) {
    LockMode m;
    for (const char *text : {
             "screenLock is offset", "screenLock is not off",
             "screenLock is not immediate", "screenLock is error 30 seconds",
             "screenLock is 30 secondhand", "screenLock is 30 seconds junk",
             "screenLock is 30seconds", "screenLock is 2147483648 seconds",
             "screenLock is 999999999999999999999999999 seconds",
             "screenLock is\n2026-01-01 error: off"}) {
        CHECK(!parseLockMode(text, &m), "reject misleading lock text: %s", text);
    }
    CHECK(parseLockMode("screenLock is 30 seconds\nwarning: coffee", &m) &&
          m.kind == LockKind::Seconds && m.seconds == 30,
          "unrelated log line cannot turn a numeric mode off");
    CHECK(parseLockMode("screenLock is off\nscreenLock delay is immediate", &m) &&
          m.kind == LockKind::Immediate, "last status wins");
    CHECK(parseLockMode("screenLock is 2147483647 seconds", &m) &&
          m.seconds == INT_MAX, "largest supported lock delay");
    CHECK(!parseLockMode("screenLock is off", nullptr), "null lock output");
    CHECK(!parseLockMode(std::string("screenLock is off\0junk", 22), &m),
          "embedded NUL in lock status");

    int v = 99;
    for (const char *text : {
             "SleepDisabled 2", "SleepDisabled -1", "SleepDisabled 1junk",
             "SleepDisabled 1 0", "SleepDisabled 99999999999999999999999999",
             "SleepDisabled 0\nSleepDisabled nonsense", "SleepDisabled1"}) {
        v = 99;
        CHECK(!parseSleepDisabledOutput(text, &v) && v == 99,
              "reject malformed boolean without committing: %s", text);
    }
    CHECK(parseSleepDisabledOutput("SleepDisabled 1\r\n", &v) && v == 1,
          "CRLF status accepted");
    CHECK(parseSleepDisabledOutput("SleepDisabled 1\nSleepDisabledExtra 0", &v) &&
          v == 1, "longer key ignored");
    CHECK(!parseSleepDisabledOutput("SleepDisabled 1", nullptr), "null sleep output");
    bool malformed = false;
    CHECK(!parseSleepDisabledOutput("SleepDisabled broken", &v, &malformed) &&
          malformed, "malformed status cannot fall back to an absent-key guess");
    CHECK(!parseSleepDisabledOutput("unrelated row", &v, &malformed) && !malformed,
          "genuinely absent status is distinct from malformed status");
    CHECK(!parseSleepDisabledOutput(std::string("SleepDisabled 1\0junk", 20), &v),
          "embedded NUL in pmset output");

    double n = 42;
    CHECK(!parseNumericPreference(std::string("1\0junk", 6), &n) && n == 42,
          "numeric embedded NUL rejected without committing");
    CHECK(!parseNumericPreference("1", nullptr), "null numeric output");
    CHECK(parseDuration(nullptr) == -1, "null duration");
    CHECK(parseDuration("0x10") == -1 && parseDuration("+0X10") == -1,
          "hex durations rejected");
    CHECK(parseDuration("1e-9999") == -1, "underflow rejected, not treated as zero");
    CHECK(parseDuration("1.25s") == 1.25, "fractional seconds preserved");
    CHECK(parseDuration("2H") == 7200.0, "uppercase duration suffix");
    CHECK(parseDuration("3650d") == 315360000.0, "duration upper boundary");
    CHECK(durationMilliseconds(1.25) == 1250, "fractional deadline kept");
    CHECK(durationMilliseconds(1.0001) == 1001, "deadline rounds up, not down");
    CHECK(durationMilliseconds(315360000.0) == 315360000000LL,
          "maximum duration fits deadline representation");

    long pid = -1;
    CHECK(parseInteger("42", 1, INT_MAX, &pid) && pid == 42, "valid integer");
    for (const char *text : {"", "0", "-1", "2147483648", "4294967297",
                             "9223372036854775808", "10junk", "1.5", "nan"}) {
        pid = -1;
        CHECK(!parseInteger(text, 1, INT_MAX, &pid) && pid == -1,
              "PID-sized range rejects %s", text);
    }
    CHECK(!parseInteger(nullptr, 1, INT_MAX, &pid), "null integer input");
    CHECK(!parseInteger("10", 1, INT_MAX, nullptr), "null integer output");
}

static void testDescriptorSafety(void) {
    ConsoleUser u = currentUser();
    int fds[2];
    CHECK(createPipe(fds), "create protected pipe");
    if (fds[0] != -1) {
        CHECK(fds[0] > 2 && fds[1] > 2, "pipe avoids stdio");
        CHECK((fcntl(fds[0], F_GETFD) & FD_CLOEXEC) &&
              (fcntl(fds[1], F_GETFD) & FD_CLOEXEC), "pipe is close-on-exec");
        close(fds[0]); close(fds[1]);
    }
    CHECK(!setNonBlocking(-1), "nonblocking setup failure is visible");
    CHECK(!setCloseOnExec(-1), "close-on-exec setup failure is visible");
    // Every combination of initially closed standard descriptors.
    for (int mask = 1; mask < 8; ++mask) {
        fflush(nullptr);
        pid_t child = fork();
        CHECK(child != -1, "fork descriptor test %d", mask);
        if (child == -1) continue;
        if (child == 0) {
            for (int fd = 0; fd <= 2; ++fd)
                if (mask & (1 << fd)) close(fd);
            CommandResult r = runCapturedAsUser(u, {"/bin/echo", "stdio-safe"}, 1500);
            _exit(r.launched && !r.timedOut && r.exitCode == 0 &&
                  r.output == "stdio-safe\n" ? 0 : 1);
        }
        int status = 0;
        bool running = false;
        bool reaped = waitForChildTimed(child, &status, 4000, &running);
        if (running) { kill(child, SIGKILL); waitForChild(child, &status); }
        CHECK(reaped && WIFEXITED(status) && WEXITSTATUS(status) == 0,
              "closed-stdio mask %d preserves child output", mask);
    }
}

static void testCaptureEdgeCases(void) {
    ConsoleUser u = currentUser();
    int64_t start = monotonicMilliseconds();
    CommandResult r = runCapturedAsUser(u, {"/usr/bin/yes"}, 250);
    int64_t elapsed = monotonicMilliseconds() - start;
    CHECK(r.timedOut && r.outputTruncated && r.output.size() == 65536,
          "continuous output remains capped and reaches its timeout");
    CHECK(elapsed < 4000, "continuous writer stopped within bound (%lld ms)",
          (long long)elapsed);
    printf("continuous-output timeout: %lld ms (250 ms budget)\n", (long long)elapsed);

    r = runCapturedAsUser(u, {"/bin/sh", "-c", "exec /bin/sleep 10"}, 0);
    CHECK(r.timedOut, "zero subprocess budget is enforced");
    r = runCapturedAsUser(u, {"/bin/echo", "short"});
    CHECK(!r.outputTruncated && r.output == "short\n", "short output is complete");
    r = runCapturedAsUser(u, {});
    CHECK(!r.launched && r.exitCode == -1, "empty command is not launched");

    pid_t child = fork();
    CHECK(child != -1, "fork bad-descriptor test");
    if (child == 0) { sleep(10); _exit(0); }
    if (child > 0) {
        r = collectChild(child, -1, 200, false);
        CHECK(r.exitCode == -1, "bad capture descriptor cannot report success");
        int status = 0;
        CHECK(waitpid(child, &status, WNOHANG) == -1 && errno == ECHILD,
              "bad-descriptor child was reaped");
    }
}

static void testPasswordPlumbing(void) {
    ConsoleUser u = currentUser();
    Secret secret;
    const char *sentinel = "test-only-fake-password-123";
    strcpy(secret.bytes, sentinel);
    secret.length = strlen(sentinel);
    CommandResult r = runPasswordCommandAsUser(u, secret,
        {"/bin/sh", "-c", "IFS= read -r p; [ \"$p\" = test-only-fake-password-123 ]"},
        3000);
    CHECK(r.launched && !r.timedOut && r.exitCode == 0,
          "fake password delivered via private terminal");
    CHECK(r.output.empty(), "private-terminal transcript is erased");
    clearSecret(&secret);
    bool zero = true;
    for (char c : secret.bytes) zero = zero && c == 0;
    CHECK(zero && secret.length == 0 && !secret.locked, "secret cleared");
    // These are synthetic test strings, never an actual login password.
}

static void testPolicyMarker(void) {
    char temp[] = "/tmp/kafueineto-marker.XXXXXX";
    char *dir = mkdtemp(temp);
    CHECK(dir != nullptr, "create marker test directory");
    if (!dir) return;
    std::string path = std::string(dir) + "/policy.state";
    const char *savedPath = kPolicyStatePath;
    Config savedCfg = cfg;
    kPolicyStatePath = path.c_str();
    cfg.lockOverride = false;
    cfg.hardNoSleep = true;  // the marker lists only the layers in use
    CHECK(writePolicyStateMarker(), "write recovery marker");
    struct stat st = {};
    CHECK(lstat(path.c_str(), &st) == 0 && (st.st_mode & 0777) == 0600,
          "marker permissions are owner-only");
    std::string before;
    FILE *f = fopen(path.c_str(), "rb");
    CHECK(f != nullptr, "read recovery marker");
    if (f) {
        char buf[1024];
        size_t n;
        while ((n = fread(buf, 1, sizeof buf, f)) > 0) before.append(buf, n);
        fclose(f);
    }
    CHECK(!writePolicyStateMarker(), "existing marker is never overwritten");
    std::string after;
    f = fopen(path.c_str(), "rb");
    if (f) {
        char buf[1024];
        size_t n;
        while ((n = fread(buf, 1, sizeof buf, f)) > 0) after.append(buf, n);
        fclose(f);
    }
    CHECK(before == after && !before.empty(), "original recovery data preserved");
    CHECK(removePolicyStateMarker(), "remove verified test marker");
    CHECK(removePolicyStateMarker(), "removal is idempotent");
    CHECK(symlink("missing", path.c_str()) == 0, "create dangling marker link");
    CHECK(!writePolicyStateMarker(), "dangling marker link is not followed");
    CHECK(lstat(path.c_str(), &st) == 0 && S_ISLNK(st.st_mode),
          "failed exclusive create preserves existing link");
    unlink(path.c_str());
    CHECK(mkfifo(path.c_str(), 0600) == 0, "create marker-path FIFO");
    CHECK(!writePolicyStateMarker(), "existing FIFO fails without blocking");
    unlink(path.c_str());
    cfg = savedCfg;
    kPolicyStatePath = savedPath;
    rmdir(dir);

    ConsoleUser u = currentUser();
    for (const std::string &text : {std::string(""), std::string("plain-name"),
                                   std::string("a'b; $(printf injected)\nspace ")}) {
        CommandResult r = runCapturedAsUser(u,
            {"/bin/sh", "-c", "printf '%s' " + shellQuote(text)});
        CHECK(r.exitCode == 0 && r.output == text,
              "recovery shell quoting preserves literal input");
    }
}

static void testParserFuzz(void) {
    // Deterministic generated byte strings, including NUL and non-ASCII.
    uint64_t state = 0x4b41465545494e45ULL;
    auto next = [&state]() {
        state ^= state << 13; state ^= state >> 7; state ^= state << 17;
        return state;
    };
    bool valid = true;
    for (int i = 0; i < 20000; ++i) {
        std::string input;
        size_t length = next() % 128;
        for (size_t j = 0; j < length; ++j) input += (char)(next() & 255);
        LockMode mode;
        if (parseLockMode(input, &mode))
            valid = valid && mode.kind != LockKind::Invalid && mode.seconds >= 0;
        int bit = -1;
        if (parseSleepDisabledOutput(input, &bit)) valid = valid && (bit == 0 || bit == 1);
        double number = 0;
        if (parseNumericPreference(input, &number)) valid = valid && std::isfinite(number);
        double duration = parseDuration(input.c_str());
        valid = valid && (duration == -1 ||
                         (std::isfinite(duration) && duration >= 0 && duration <= 315360000));
    }
    CHECK(valid, "20,000 generated parser inputs preserve output invariants");
}

// The real argument parser, one forked child per scenario: parseArgs exits
// on bad input, and getopt keeps global state, so a child is the only way
// to run the exact production code path repeatedly. Nothing beyond parsing
// runs (no assertions, no policy changes).
struct CliCase {
    std::vector<const char *> args;
    int exitCode;
    const char *expect;             // must appear in stdout+stderr
    const char *reject = nullptr;   // must not appear
};

static void testCommandLine(void) {
    char pidText[32];
    snprintf(pidText, sizeof pidText, "%ld", (long)getpid());
    char pidExpect[48];
    snprintf(pidExpect, sizeof pidExpect, "waitpid=%ld", (long)getpid());
    const CliCase cases[] = {
        {{}, 0, "lock=0 display=0 strong=0 presence=0 mouse=0 hard=0 probe=0"},
        {{"--help"}, 0, "Presets"},
        {{"-h"}, 0, "Usage: kafueineto"},
        {{"--version"}, 0, "kafueineto 2.0.0"},
        // Presets nest: -e is -a plus -L, -a is -x plus -H, -x is -d -s -p -m.
        {{"-x"}, 0, "lock=0 display=1 strong=1 presence=1 mouse=1 hard=0"},
        {{"--rootless"}, 0, "lock=0 display=1 strong=1 presence=1 mouse=1 hard=0"},
        {{"-a"}, 0, "lock=0 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"--all"}, 0, "lock=0 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"-e"}, 0, "lock=1 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"--everything"}, 0, "lock=1 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"-x", "-a"}, 0, "lock=0 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"-a", "-e"}, 0, "lock=1 display=1 strong=1 presence=1 mouse=1 hard=1"},
        {{"-e", "-x"}, 0, "lock=1 display=1 strong=1 presence=1 mouse=1 hard=1"},
        // One flag per method; nothing is implied between them.
        {{"-d"}, 0, "lock=0 display=1 strong=0 presence=0 mouse=0 hard=0"},
        {{"--display"}, 0, "display=1 strong=0"},
        {{"-s"}, 0, "lock=0 display=0 strong=1 presence=0 mouse=0 hard=0"},
        {{"--strong"}, 0, "strong=1 presence=0"},
        {{"-p"}, 0, "lock=0 display=0 strong=0 presence=1 mouse=0 hard=0"},
        {{"--presence"}, 0, "presence=1 mouse=0"},
        {{"-m"}, 0, "lock=0 display=0 strong=0 presence=0 mouse=1 hard=0"},
        {{"--mouse"}, 0, "presence=0 mouse=1"},
        {{"-H"}, 0, "lock=0 display=0 strong=0 presence=0 mouse=0 hard=1"},
        {{"--hard-no-sleep"}, 0, "mouse=0 hard=1"},
        {{"-L"}, 0, "lock=1 display=0 strong=0 presence=0 mouse=0 hard=0"},
        {{"--no-auto-lock"}, 0, "lock=1 display=0"},
        {{"-d", "-p", "-A"}, 0, "lock=0 display=1 strong=0 presence=1 mouse=0 hard=0 probe=0 aconly=1"},
        {{"-dspm"}, 0, "display=1 strong=1 presence=1 mouse=1 hard=0"},
        // The lock override is all-or-nothing for the run.
        {{"-L", "-A"}, 2, "cannot be combined"},
        {{"-A", "-L"}, 2, "cannot be combined"},
        {{"-L", "-b", "20"}, 2, "cannot be combined"},
        {{"-e", "-A"}, 2, "cannot be combined"},
        {{"-e", "-b", "50"}, 2, "cannot be combined"},
        // Everything else composes with the power options.
        {{"-a", "-A"}, 0, "hard=1 probe=0 aconly=1"},
        {{"-a", "-b", "20"}, 0, "aconly=0 minbat=20"},
        {{"-x", "-A", "-b", "20"}, 0, "redundant"},
        {{"--ac-only", "--min-battery", "20"}, 0, "redundant"},
        // --idle only matters with a presence method.
        {{"-i", "2m"}, 0, "idle=120"},
        {{"-i", "2m"}, 0, "only matters with -p or -m"},
        {{"-p", "-i", "2m"}, 0, "presence=1 mouse=0 hard=0 probe=0 aconly=0 minbat=0 idle=120",
         "only matters"},
        {{"-m", "--idle", "5s"}, 0, "idle=5", "only matters"},
        {{"--idle", "4.99"}, 2, "--idle needs a duration"},
        // Removed flags are gone, not silently accepted.
        {{"--no-jiggle"}, 2, "--help"},
        {{"-n"}, 2, "--help"},
        {{"--drift"}, 2, "--help"},
        {{"--request-permission"}, 2, "--help"},
        {{"--max"}, 2, "--help"},
        {{"--all-rootless"}, 2, "--help"},
        {{"--aggressive"}, 2, "--help"},
        {{"--resist-all-sleep"}, 2, "--help"},
        {{"--idle-probe"}, 2, "--help"},
        // Diagnostics validate the rest of the line before running.
        {{"--probe"}, 0, "probe=1"},
        {{"--probe", "--unknown"}, 2, "--help"},
        {{"--probe", "unwanted"}, 2, "unexpected argument"},
        {{"--probe", "--help"}, 0, "Usage:"},
        // Durations.
        {{"-d", "-t", "2H"}, 0, "display=1 strong=0 presence=0 mouse=0 hard=0 probe=0 aconly=0 minbat=0 idle=120 timeout=7200"},
        {{"--timeout", "1.25"}, 0, "timeout=1.25"},
        {{"-t", "1.25s"}, 0, "timeout=1.25"},
        {{"--timeout", "3650d"}, 0, "timeout=315360000"},
        {{"--timeout", "0"}, 2, "--timeout needs a duration"},
        {{"--timeout", "0.999"}, 2, "--timeout needs a duration"},
        {{"--timeout", "3651d"}, 2, "--timeout needs a duration"},
        {{"--timeout", "nan"}, 2, "--timeout needs a duration"},
        {{"--timeout", "0x10"}, 2, "--timeout needs a duration"},
        {{"--timeout", "1e999"}, 2, "--timeout needs a duration"},
        {{"--timeout"}, 2, "--help"},
        // Battery threshold.
        {{"--min-battery", "100"}, 0, "minbat=100"},
        {{"--min-battery", "0"}, 2, "whole number"},
        {{"--min-battery", "101"}, 2, "whole number"},
        {{"--min-battery", "1.5"}, 2, "whole number"},
        // Process watch.
        {{"--waitpid", pidText}, 0, pidExpect},
        {{"-w", "0"}, 2, "positive process ID"},
        {{"--waitpid", "-1"}, 2, "positive process ID"},
        {{"--waitpid", "4294967297"}, 2, "positive process ID"},
        {{"--waitpid", "9223372036854775808"}, 2, "positive process ID"},
        {{"--waitpid", "1x"}, 2, "positive process ID"},
        {{"--waitpid", "1.5"}, 2, "positive process ID"},
        // Output control and leftovers.
        {{"-vv", "-q"}, 0, "quiet=1 verbose=2"},
        {{"--", "unexpected"}, 2, "unexpected argument"},
        {{"-Q"}, 2, "--help"},
        // Background verbs: one trailing word, anywhere on the line.
        {{"on"}, 0, "verbose=0 cmd=1"},
        {{"-x", "on"}, 0, "display=1 strong=1 presence=1 mouse=1 hard=0 probe=0 aconly=0 minbat=0 idle=120 timeout=0 waitpid=0 quiet=0 verbose=0 cmd=1"},
        {{"on", "-d", "-t", "5m"}, 0, "display=1 strong=0 presence=0 mouse=0 hard=0 probe=0 aconly=0 minbat=0 idle=120 timeout=300 waitpid=0 quiet=0 verbose=0 cmd=1"},
        {{"off"}, 0, "cmd=2"},
        {{"status"}, 0, "cmd=3"},
        {{"status", "-v"}, 0, "verbose=1 cmd=3"},
        {{"-q", "off"}, 0, "quiet=1 verbose=0 cmd=2"},
        {{"off", "-x"}, 2, "takes no options"},
        {{"-t", "5", "off"}, 2, "takes no options"},
        {{"status", "-d"}, 2, "takes no options"},
        {{"on", "off"}, 2, "unexpected argument 'off'"},
        {{"start"}, 2, "unexpected argument 'start'"},
        {{"--probe", "on"}, 2, "cannot be combined"},
        {{"--help"}, 0, "kafueineto off | status"},
    };

    for (const CliCase &c : cases) {
        std::string label = "kafueineto";
        for (const char *a : c.args) label += std::string(" ") + a;
        int fds[2];
        CHECK(createPipe(fds), "pipe for '%s'", label.c_str());
        if (fds[0] == -1) continue;
        fflush(nullptr);
        pid_t child = fork();
        CHECK(child != -1, "fork for '%s'", label.c_str());
        if (child == -1) { close(fds[0]); close(fds[1]); continue; }
        if (child == 0) {
            dup2(fds[1], STDOUT_FILENO);
            dup2(fds[1], STDERR_FILENO);
            close(fds[0]); close(fds[1]);
            cfg = Config{};
            optind = 1;
            optreset = 1;
            std::vector<char *> argv;
            argv.push_back(const_cast<char *>("kafueineto"));
            for (const char *a : c.args) argv.push_back(const_cast<char *>(a));
            argv.push_back(nullptr);
            parseArgs((int)argv.size() - 1, argv.data());
            printf("lock=%d display=%d strong=%d presence=%d mouse=%d hard=%d "
                   "probe=%d aconly=%d minbat=%d "
                   "idle=%.9g timeout=%.9g waitpid=%ld quiet=%d verbose=%d "
                   "cmd=%d\n",
                   cfg.lockOverride, cfg.display, cfg.strong, cfg.presence,
                   cfg.mouse, cfg.hardNoSleep, cfg.probe, cfg.acOnly,
                   cfg.minBattery, cfg.idleThreshold, cfg.timeout,
                   (long)cfg.waitPid, cfg.quiet, cfg.verbose, (int)cfg.command);
            fflush(stdout);
            _exit(0);
        }
        close(fds[1]);
        std::string output;
        char buffer[4096];
        for (;;) {
            ssize_t n = read(fds[0], buffer, sizeof buffer);
            if (n > 0) { output.append(buffer, (size_t)n); continue; }
            if (n == -1 && errno == EINTR) continue;
            break;
        }
        close(fds[0]);
        int status = 0;
        bool reaped = waitForChild(child, &status);
        int code = reaped && WIFEXITED(status) ? WEXITSTATUS(status) : -1;
        bool found = output.find(c.expect) != std::string::npos;
        bool clean = !c.reject || output.find(c.reject) == std::string::npos;
        CHECK(code == c.exitCode && found && clean,
              "'%s': want exit %d with '%s'%s%s; got exit %d: %s",
              label.c_str(), c.exitCode, c.expect,
              c.reject ? " and without " : "", c.reject ? c.reject : "",
              code, output.c_str());
    }
}

// The background-instance registry: stale records (dead pid, or a pid that
// now belongs to some other program) are dropped and deleted, and nothing is
// ever signalled from here.
static void testDaemonRegistry(void) {
    char temp[] = "/tmp/kafueineto-registry.XXXXXX";
    char *dir = mkdtemp(temp);
    CHECK(dir != nullptr, "create registry test directory");
    if (!dir) return;
    std::string root = dir;
    CHECK(makeDirectories(root + "/a/b/c", 0755), "mkdir -p creates nested dirs");
    struct stat st = {};
    CHECK(stat((root + "/a/b/c").c_str(), &st) == 0 && S_ISDIR(st.st_mode),
          "nested directory exists");
    CHECK(makeDirectories(root + "/a/b/c", 0755), "mkdir -p is idempotent");

    pid_t dead = 99999;
    while (dead > 2 && !(kill(dead, 0) == -1 && errno == ESRCH)) dead--;
    bool known = false;
    CHECK(!isKafueinetoProcess(getpid(), &known) && known,
          "the test harness is not mistaken for kafueineto");
    CHECK(!isKafueinetoProcess(dead, &known) && !known,
          "a dead pid is unknown");

    std::string registry = root + "/daemons";
    CHECK(makeDirectories(registry, 0755), "create registry");
    auto writeRecord = [&](const std::string &name) {
        FILE *f = fopen((registry + "/" + name).c_str(), "w");
        if (f) { fputs("  command test\n", f); fclose(f); }
    };
    writeRecord(std::to_string((long long)getpid()));  // alive, not kafueineto
    writeRecord(std::to_string((long long)dead));      // gone
    writeRecord("notapid");                            // ignored
    std::vector<DaemonRecord> records;
    scanRegistryDir(registry, &records);
    CHECK(records.size() == 2, "two numeric records scanned, got %zu",
          records.size());
    bool allStale = !records.empty();
    for (const DaemonRecord &r : records)
        allStale = allStale && r.state == DaemonRecord::Stale;
    CHECK(allStale, "both records are stale");
    CHECK(access((registry + "/" + std::to_string((long long)getpid())).c_str(),
                 F_OK) == -1 && errno == ENOENT,
          "stale record of a reused pid is deleted");
    CHECK(access((registry + "/" + std::to_string((long long)dead)).c_str(),
                 F_OK) == -1, "stale record of a dead pid is deleted");
    CHECK(access((registry + "/notapid").c_str(), F_OK) == 0,
          "non-record files are left alone");
    records.clear();
    scanRegistryDir(root + "/missing", &records);
    CHECK(records.empty(), "missing registry scans as empty");

    unsetenv("SUDO_UID");
    CHECK(invokingUid() == getuid(), "invoking uid without sudo is our uid");
    CHECK(!homeOf(getuid()).empty() && homeOf(getuid())[0] == '/',
          "home directory resolved");
    uid_t unknown = 2000000000;  // -2 is nobody on macOS, with a real home
    while (unknown < 2000001000 && !homeOf(unknown).empty()) unknown++;
    CHECK(homeOf(unknown).empty(), "unknown uid has no home");

    unlink((registry + "/notapid").c_str());
    rmdir(registry.c_str());
    rmdir((root + "/a/b/c").c_str());
    rmdir((root + "/a/b").c_str());
    rmdir((root + "/a").c_str());
    rmdir(root.c_str());
}

int main(void) {
    testCommandLine();
    testDaemonRegistry();
    testParseLockMode();
    testParseSleepDisabledOutput();
    testParseDuration();
    testParseNumericPreference();
    testCollectChild();
    testDefaultsPipeline();
    testDomainFileScan();
    testSystemReadOnly();
    testParserHardening();
    testDescriptorSafety();
    testCaptureEdgeCases();
    testPasswordPlumbing();
    testPolicyMarker();
    testParserFuzz();
    printf("%d checks, %d failures\n", gChecks, gFailures);
    return gFailures ? 1 : 0;
}
