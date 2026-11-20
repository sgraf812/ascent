#!/usr/bin/env python3
"""Record the bench in bench/results.csv, or compare two recorded commits.

  scripts/bench-record.py [FILE...]        run the families of FILE... (default: all), append rows
  scripts/bench-record.py --compare [A [B]] compare the instructions of commit B against commit A
                                           (default: the last two recorded commits), with the
                                           significance checks of radar

Each row is `date,commit,family,size,phase,instructions,ms`. The driver writes the rows, and the
instruction counts come from the hardware counter of bench/ffi/instructions.c. The commit of a run on
a tree with changes other than bench/results.csv carries the suffix `+dirty`."""
import csv, datetime, os, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
CSV = BENCH / "results.csv"
HEADER = ["date", "commit", "family", "size", "phase", "instructions", "ms"]
SCOPE = ["systemd-run", "--user", "--scope", "-p", "MemorySwapMax=0", "-p", "CPUWeight=50",
         "--quiet", "timeout", "600"]


def families():
    text = (BENCH / "lakefile.lean").read_text()
    return [f"{m}.lean" for roots in re.findall(r"roots := #\[([^\]]*)\]", text)
            for m in re.findall(r"`([\w.]+)", roots)]


def commit():
    sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, check=True,
                         capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--", ".", ":!bench/results.csv"],
                           cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()
    return sha + ("+dirty" if dirty else "")


def record(files):
    if not CSV.exists():
        CSV.write_text(",".join(HEADER) + "\n")
    env = dict(os.environ, BENCH_CSV=str(CSV), BENCH_COMMIT=commit(),
               BENCH_DATE=datetime.date.today().isoformat())
    failed = []
    for f in files:
        print(f"== {f}", flush=True)
        r = subprocess.run(SCOPE + ["lake", "lean", f], cwd=BENCH, env=env)
        if r.returncode != 0:
            failed.append(f)
    if failed:
        sys.exit(f"failed: {' '.join(failed)}")


# The significance checks of radar (github.com/leanprover/radar, `MetricComparer`): the noise of a
# metric is the 0.9-quantile `q` of the absolute differences between consecutive recorded commits,
# over the last `QUANTILE_COMMITS` commits up to the first commit of the comparison. A change `d` is small, medium or large if `|d| / q`
# reaches 3, 6 or 9. A metric with fewer than `MIN_DELTAS` differences has no quantile, and its
# change counts by `|d| / v` with the thresholds 1, 3 and 10 %. A comparison is significant with at
# least 1 large change, 5 changes that are at least medium, or 20 changes. Fewer instructions are
# better.
QUANTILE = 0.9
QUANTILE_COMMITS = 50
MIN_DELTAS = 5
QUANTILE_FACTORS = (3, 6, 9)
DELTA_PERCENTS = (1, 3, 10)
SIGNIFICANT_COUNTS = (20, 5, 1)
CLASSES = ("small", "medium", "large")


def abs_quantile(xs, q):
    asc = sorted(abs(x) for x in xs)
    pos = q * (len(asc) - 1)
    i = int(pos)
    if i >= len(asc) - 1:
        return asc[-1]
    w = pos - i
    return asc[i] * (1 - w) + asc[i + 1] * w


def level(x, thresholds):
    """The class index of `x` against ascending `thresholds`, or -1 below the first one."""
    return max((i for i, t in enumerate(thresholds) if x >= t), default=-1)


def compare(a, b):
    rows = list(csv.DictReader(CSV.open()))
    commits = list(dict.fromkeys(r["commit"] for r in rows))
    if b is None:
        b = commits[-1]
    if a is None:
        a = commits[-2] if len(commits) >= 2 else sys.exit("fewer than two recorded commits")
    for c in (a, b):
        if c not in commits:
            sys.exit(f"commit {c} is not recorded")
    # The value of each metric `(family, size, phase)` at each commit; the last run of a commit counts.
    values = {}
    for r in rows:
        values.setdefault((r["family"], int(r["size"]), r["phase"]), {})[r["commit"]] = int(r["instructions"])
    # The noise is estimated before the change: on the history up to commit `a`.
    history = commits[: commits.index(a) + 1][-QUANTILE_COMMITS:]
    changes = []
    for metric, byCommit in values.items():
        if a not in byCommit or b not in byCommit:
            continue
        x, y = byCommit[a], byCommit[b]
        if x == y:
            continue
        series = [byCommit[c] for c in history if c in byCommit]
        deltas = [v - u for u, v in zip(series, series[1:])]
        if len(deltas) >= MIN_DELTAS and abs_quantile(deltas, QUANTILE) > 0:
            q = abs_quantile(deltas, QUANTILE)
            lvl, why = level(abs(y - x) / q, QUANTILE_FACTORS), f"{abs(y - x) / q:.1f} q"
        elif x != 0:
            lvl, why = level(100 * abs(y - x) / x, DELTA_PERCENTS), "no quantile"
        else:
            continue
        if lvl >= 0:
            changes.append((lvl, metric, x, y, why))
    counts = [sum(1 for c in changes if c[0] >= i) for i in range(3)]
    significant = any(n >= k for n, k in zip(counts, SIGNIFICANT_COUNTS))
    print(f"{b} against {a}: {'significant' if significant else 'not significant'}, "
          f"{counts[2]} large, {counts[1] - counts[2]} medium, {counts[0] - counts[1]} small changes")
    for lvl in (2, 1, 0):
        for _, (family, size, phase), x, y, why in sorted(
                (c for c in changes if c[0] == lvl), key=lambda c: -abs(c[3] - c[2]) / max(c[2], 1)):
            verdict = "better" if y < x else "worse"
            print(f"  {CLASSES[lvl]:6} {family}({size}) {phase}: {x / 1e9:.3f} G -> {y / 1e9:.3f} G  "
                  f"{100 * (y - x) / x:+.1f} %  {verdict}  ({why})")


def main():
    args = sys.argv[1:]
    if args and args[0] == "--compare":
        rest = args[1:]
        if len(rest) > 2:
            sys.exit(__doc__)
        compare(rest[0] if len(rest) == 2 else None, rest[-1] if rest else None)
    elif any(a.startswith("-") for a in args):
        sys.exit(__doc__)
    else:
        record(args or families())


main()
