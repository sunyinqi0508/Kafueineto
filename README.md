# kafueineto

Keep a Mac awake, with optional display protection, simulated presence, and temporary system-policy changes.

A single C++17 program. With no flags it holds an idle-sleep assertion, like `caffeinate -i`. Every further method is one flag, three presets turn several on at once, and a trailing `on` runs it in the background. Methods that need root re-run the command through sudo by themselves. Only one method ever asks for a login password, and only the preset that names it includes it.

## Build and start

Build on macOS with an Apple command-line toolchain and SDK:

```sh
make
./kafueineto --help
```

No sleep for 45 minutes, nothing else:

```sh
./kafueineto -t 45m
```

The strongest protection available without sudo, in the background:

```sh
./kafueineto -x on
./kafueineto status
./kafueineto off
```

In the foreground, press **Ctrl-C** to stop and **Ctrl-T** for a status line (elapsed time, time left, what is held, pokes and nudges posted).

## Presets

| Preset | Means | Needs |
| --- | --- | --- |
| `-x`, `--rootless` | every method that works without sudo: `-d -s -p -m` | nothing |
| `-a`, `--all` | everything that needs no password: `-x` and `-H` | sudo, asked for automatically |
| `-e`, `--everything` | `-a` and `-L` | sudo and the login password |

Presets nest, so `-e` includes `-a`, which includes `-x`. Their position on the command line does not matter.

## Methods

Each method adds to the base idle-sleep assertion.

| Method | What it does |
| --- | --- |
| `-d`, `--display` | Keep the display awake while it is on. |
| `-s`, `--strong` | Also hold the stronger system-sleep assertion, what `caffeinate -s` uses. powerd honors it on AC power only. |
| `-p`, `--presence` | Look present: after `--idle` seconds without input, reset the idle counters with an invisible null HID event. The screensaver and the "away" status in chat apps stay off. Needs the Accessibility permission. |
| `-m`, `--mouse` | Move the pointer one pixel toward the screen center after `--idle` seconds without input, for apps that watch the cursor itself. Needs the same permission. |
| `-H`, `--hard-no-sleep` | **sudo.** Set the system-wide sleep-disable setting (`pmset disablesleep`) for the run. This is the only method that also blocks lid-close and menu sleep. |
| `-L`, `--no-auto-lock` | **sudo and the login password.** Turn off the logged-in user's automatic Screen Lock and screensaver password for the run. Cannot combine with `-A` or `-b`. |

`-p` and `-m` ask macOS for the Accessibility permission at startup when it is missing. Sleep prevention works without it; only those two methods wait for it.

## Options

| Option | What it does |
| --- | --- |
| `-i`, `--idle DURATION` | Idle time before `-p` and `-m` act; default 120 s, minimum 5 s. |
| `-t`, `--timeout DURATION` | Stop after a duration; cleanup can take longer. |
| `-w`, `--waitpid PID` | Stop when an existing process exits. |
| `-A`, `--ac-only` | Pause while on battery; resume on AC power. |
| `-b`, `--min-battery PCT` | Pause below a battery percentage from 1 to 100. |
| `--probe` | Print idle, permission, power, and lid status without changing anything, then exit. |
| `-v`, `--verbose` | Show every decision. |
| `-q`, `--quiet` | Show only warnings and errors; overrides `-v`. Ctrl-T still answers. |
| `-V`, `--version`, `-h`, `--help` | Version and help. |

Durations are seconds or a number with the suffix `s`, `m`, `h`, or `d`, including uppercase suffixes and fractions: `90`, `45m`, `1.5h`, `1d`. Timeouts run from 1 second to 3650 days and start after any password prompt. With both a timeout and a process watch, whichever comes first ends the run.

The only invalid combination is `-L` (or `-e`) with `-A` or `-b`; it exits with code 2. `-A` with `-b`, and `--idle` without `-p` or `-m`, print a note.

## Background instances

| Command | What it does |
| --- | --- |
| `kafueineto [flags] on` | Start in the background. Startup messages, errors, and the `-L` password prompt still appear on the terminal; once everything is up, the pid is printed and the shell returns. |
| `kafueineto off` | Stop every background instance and wait for its settings to be restored. If a root-owned instance is running, `off` re-runs itself through sudo. Foreground instances are listed, not stopped. |
| `kafueineto status` | List background instances, foreground instances, and whether a recovery record is in use. |

A background instance logs to `~/Library/Logs/kafueineto.log`, or `/var/log/kafueineto.log` when it runs as root, and leaves a record under `~/Library/Application Support/kafueineto/daemons/` or `/var/db/kafueineto/daemons/`. Records whose process is gone, or whose pid now belongs to another program, are dropped automatically; nothing is ever signalled unless it really is a kafueineto process.

## Sudo-only methods

`-H`, `-L`, `-a`, and `-e` re-run the whole command line through `sudo` when not already root; sudo asks for your password or Touch ID the way it normally does. `-H` temporarily changes the system sleep-disable setting. `-L` additionally needs the logged-in user's login password, typed privately on the terminal, and temporarily changes that user's automatic-lock and screensaver settings; it needs a macOS release whose `sysadminctl -screenLock` works.

These methods are **not necessary for ordinary sleep prevention**. `-H`, `-a`, and `-e` may keep a closed laptop running: keep it ventilated and never put it in a bag while active. With `-L` or `-e`, do not leave the machine unattended. No method unlocks a locked session, promises to prevent every kind of sleep, or overrides hardware safety limits.

### Recovery

Before any persistent change, the program records the original values and the commands to restore them in:

```text
/var/db/kafueineto-policy.state
```

A detached watchdog restores the settings after a normal exit, a signal, a timeout, or a parent crash, and removes the file once restoration is verified. The file is expected while an instance with sudo methods is running; `status` and `off` say so. If it remains with no instance running, restoration was not confirmed:

```sh
sudo cat /var/db/kafueineto-policy.state
```

Restore the listed values, verify them, and only then remove the file. Sudo methods refuse to start while it exists; do not delete it just to get past that check.

### Known limitations

- The watchdog is a forked child that does not exec. It stays on plain system calls, libc, and C++ containers, and macOS makes malloc fork-safe, but Apple still documents allocation between fork and exec in a multithreaded process as a deadlock risk. Only an exec-launched helper would remove it entirely.
- Parent and watchdog coordinate restoration through a pipe, process state, and a grace period, not a transactional protocol. Interruption at every mutation boundary has not been fault-injection tested.
- The effective lock policy is read from `sysadminctl` text output and a private session-status key. Compatibility with a given macOS release, managed device, console switch, or display setup needs testing on that setup.
- Float preferences round-trip through the text interface of `defaults`, so they are compared within a tolerance, not bit for bit.
- With `-L`, the effective lock setting is polled once a second through `sysadminctl`; the six screensaver preferences are swept every 15 seconds and whenever their preference directories change.
- Under sudo, `-p` retries each poke with the console user's credentials if the first attempt is refused, and `-m` posts as root. Neither has been verified while running as root; the sleep-related methods are unaffected.

## Tests

```sh
make test            # native suite, no sudo
make test-sanitize   # the same under AddressSanitizer and UBSan
```

The suite compiles the real source with `main` renamed and exercises the parsers, the subprocess plumbing, the recovery marker, the background-instance registry, and the command-line parser (each scenario in a forked child). It reads system status but writes only a per-process `com.kafueineto.test.*` preference domain and private temporary directories. It does not change real screen-lock or sleep settings, and it is not a live watchdog crash test; before relying on `-H` or `-L`, exercise normal exit, timeout, signals, parent kill, power transitions, and logout on a test Mac and verify the original values after each.

## Installation and exit codes

```sh
sudo make install
make install DESTDIR=/tmp/stage PREFIX=/usr/local   # staged
```

`CXX`, `CXXFLAGS`, `CPPFLAGS`, `LDFLAGS`, `LDLIBS`, `PREFIX`, and `DESTDIR` can be passed to `make`. `make clean` removes only this project's build products.

Exit code **0** is a normal stop, **1** a runtime or cleanup error, and **2** invalid usage. Investigate a runtime or cleanup error rather than assuming settings were restored.
