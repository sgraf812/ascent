#!/usr/bin/env python3
"""Record the bench in bench/results.csv, or compare two recorded commits.

  scripts/bench-record.py [FILE...]        run the families of FILE... (default: all), append rows
  scripts/bench-record.py --compare [A [B]] compare the instructions of commit B against commit A
                                           (default: the last two recorded commits)

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


def compare(a, b):
    rows = list(csv.DictReader(CSV.open()))
    commits = list(dict.fromkeys(r["commit"] for r in rows))
    if b is None:
        b = commits[-1]
    if a is None:
        a = commits[-2] if len(commits) >= 2 else sys.exit("fewer than two recorded commits")
    def total(c):
        # The last run of a commit counts.
        return {(r["family"], int(r["size"])): int(r["instructions"])
                for r in rows if r["commit"] == c and r["phase"] == "total"}
    ta, tb = total(a), total(b)
    print(f"instructions of {b} against {a}")
    for key in sorted(set(ta) & set(tb)):
        x, y = ta[key], tb[key]
        print(f"  {key[0]}({key[1]}): {x / 1e9:.2f} G -> {y / 1e9:.2f} G  {100 * (y - x) / x:+.1f} %")


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
