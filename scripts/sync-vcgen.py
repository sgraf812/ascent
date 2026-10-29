#!/usr/bin/env python3
"""Regenerate `Ascent/Tactic/VCGen/` from the `vcgen` sources of the pinned toolchain.

Each translated module is copied from the toolchain, rewritten by the translation table `RULES`
(T1 to T4 of `docs/vcgen-fork.md`), and then patched by `patches/vcgen/series`.

Usage: `scripts/sync-vcgen.py` writes the tree. `scripts/sync-vcgen.py --check` fails if the
committed tree differs from the regenerated one.
"""

import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "Ascent" / "Tactic" / "VCGen"
PATCHES = ROOT / "patches" / "vcgen"

# Translated modules, in import order.
MODULES = ["RuleConstruction", "RuleCache", "Solve", "Driver"]

RULES = [
    # T1. Names.
    (r"^namespace Lean\.Elab\.Tactic\.VCGen$", "namespace Lean.Elab.Tactic.VCGen.Ascend"),
    (r"^end Lean\.Elab\.Tactic\.VCGen$", "end Lean.Elab.Tactic.VCGen.Ascend"),
    # T2. Module headers.
    (r"^module\n", ""),
    (r"^prelude\n", ""),
    (r"^(public )?(meta )?import ", "import "),
    (r"^(\s*)public (section|def|partial def|structure|inductive|abbrev|instance|theorem)\b",
     r"\1\2"),
    (r"^(@\[[^\]]*\] )public ", r"\1"),
    # T3. Goal metadata.
    (r"\bWPApp\b", "WRPApp"),
    (r"\bisWPApp\?", "isWRPApp?"),
    (r"info\.args\.take 7", "info.lemmaPrefix"),
    (r"\.set! 7 ", ".set! WRPApp.progIdx "),
    (r"getArg! 7", "getArg! WRPApp.progIdx"),
    (r"setAppArg rhs 7 ", "setAppArg rhs WRPApp.progIdx "),
    # T4. Lemmas.
    (r"``Std\.WP\.Triple\.intro\b", "``Ascent.Refinement.intro"),
    (r"``Triple\b", "``Ascent.Refinement"),
    (r"\bunfoldTriple\b", "unfoldRefinement"),
    (r"``WP\.wp_monotone_post_le\b", "``Ascent.wrp_mono_post_le"),
    (r"``WP\.wp_monotone_epost_le\b", "``Ascent.wrp_mono_erel_le"),
    (r"``WP\.wp_monotone_bot_le\b", "``Ascent.wrp_mono_bot_le"),
    (r"``Std\.WP\.wp_le_wp_of_eq\b", "``Ascent.wrp_le_wrp_of_eq"),
    (r"\btripleToWpProof\?", "refinementToWrpProof?"),
]

# Imports of a translated sibling import the translated module as well as the original.
SIBLING_IMPORT = re.compile(r"^import Lean\.Elab\.Tactic\.VCGen\.(\w+)$", re.M)


def toolchain_src() -> pathlib.Path:
    prefix = subprocess.run(["lean", "--print-prefix"], cwd=ROOT, check=True,
                            capture_output=True, text=True).stdout.strip()
    return pathlib.Path(prefix) / "src" / "lean" / "Lean" / "Elab" / "Tactic" / "VCGen"


def translate(text: str) -> str:
    for pat, rep in RULES:
        text = re.sub(pat, rep, text, flags=re.M)

    def sibling(m: re.Match) -> str:
        line = m.group(0)
        if m.group(1) in MODULES:
            return line + "\nimport Ascent.Tactic.VCGen." + m.group(1)
        return line

    text = SIBLING_IMPORT.sub(sibling, text)
    # Every translated module sees the hand-written metadata and lemmas.
    return text.replace("\nimport ", "\nimport Ascent.Tactic.VCGen.Shim\nimport ", 1)


def generate(dest: pathlib.Path, patches: bool = True) -> None:
    src = toolchain_src()
    dest.mkdir(parents=True, exist_ok=True)
    for mod in MODULES:
        (dest / f"{mod}.lean").write_text(translate((src / f"{mod}.lean").read_text()))
    series = PATCHES / "series"
    if patches and series.exists():
        for name in series.read_text().split():
            subprocess.run(["patch", "--quiet", "-p1", "-d", str(dest.parent.parent.parent),
                            "-i", str(PATCHES / name)], check=True)


def main() -> None:
    if "--check" in sys.argv:
        with tempfile.TemporaryDirectory() as tmp:
            tree = pathlib.Path(tmp) / "Ascent" / "Tactic" / "VCGen"
            generate(tree)
            diff = subprocess.run(["diff", "-r", "-q", str(tree), str(OUT),
                                   "-x", "Shim.lean", "-x", "WRPApp.lean", "-x", "Frontend.lean"])
            sys.exit(diff.returncode)
    if "--raw" in sys.argv:
        generate(pathlib.Path(sys.argv[sys.argv.index("--raw") + 1]), patches=False)
        return
    generate(OUT)


if __name__ == "__main__":
    main()
