#!/usr/bin/env python3
"""Regenerate one patch of `patches/vcgen/series` from the committed tree.

`scripts/refresh-patch.py D8-wrp-spec-rules.patch` takes `Ascent/Tactic/VCGen/` as the intended
result of the whole series, reverse-applies the patches after the named one to it, and diffs the
outcome against the raw translation with the patches before the named one applied. The named patch
is rewritten with that diff. `scripts/sync-vcgen.py --check` then validates the series.
"""
import pathlib
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sync = __import__("sync-vcgen")

ROOT = sync.ROOT
OUT = sync.OUT
PATCHES = sync.PATCHES
REL = pathlib.Path("Ascent") / "Tactic" / "VCGen"


def apply(patches: list[str], root: pathlib.Path, reverse: bool = False) -> None:
    for name in patches:
        subprocess.run(["patch", "--quiet", "--no-backup-if-mismatch", "-p1", "-d", str(root)]
                       + (["-R"] if reverse else []),
                       stdin=(PATCHES / name).open(), check=True)


def main() -> None:
    name = sys.argv[1]
    series = [l.strip() for l in (PATCHES / "series").read_text().splitlines() if l.strip()]
    k = series.index(name)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        before = tmp / "a"
        after = tmp / "b"
        (before / REL).parent.mkdir(parents=True)
        (after / REL).parent.mkdir(parents=True)
        sync.generate(before / REL, patches=False)
        apply(series[:k], before)
        shutil.copytree(OUT, after / REL)
        apply(list(reversed(series[k + 1:])), after, reverse=True)
        text = ""
        for mod in sync.MODULES:
            rel = REL / f"{mod}.lean"
            diff = subprocess.run(["diff", "-uN", f"a/{rel}", f"b/{rel}"],
                                  capture_output=True, text=True, cwd=tmp)
            if diff.stdout:
                text += f"diff -ruN a/{rel} b/{rel}\n" + diff.stdout
        (PATCHES / name).write_text(text)
    print(f"rewrote {name}")


if __name__ == "__main__":
    main()
