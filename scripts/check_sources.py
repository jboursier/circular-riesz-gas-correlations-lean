#!/usr/bin/env python3
"""Sweep the Lean sources for constructs that would weaken what the build certifies.

Comments and string literals are ignored. The script fails on `sorry`, `admit`, `axiom`
and `opaque` declarations, `native_decide`, `implemented_by`, `extern`, kernel type-check
bypasses, and heartbeat or recursion-depth overrides. The only exception is the comparator
challenges `Riesz2Audit/*/Challenge.lean`: each one must contain exactly one `sorry`, the proof
of its final theorem.

Usage: python3 scripts/check_sources.py [ROOT]
Exit status: 0 if no forbidden construct is found, 1 otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

FORBIDDEN = [
    (re.compile(r"\bsorry\b"), "`sorry`"),
    (re.compile(r"\badmit\b"), "`admit`"),
    (re.compile(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|public|noncomputable|unsafe)\s+)*axiom\b"),
     "`axiom` declaration"),
    (re.compile(r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|public|noncomputable|unsafe)\s+)*opaque\b"),
     "`opaque` declaration"),
    (re.compile(r"\bnative_decide\b"), "`native_decide`"),
    (re.compile(r"\bimplemented_by\b"), "`implemented_by`"),
    (re.compile(r"@\[\s*extern\b"), "`extern`"),
    (re.compile(r"\bdebug\.skipKernelTC\b"), "kernel type-check bypass"),
    (re.compile(r"\bset_option\s+(?:synthInstance\.)?maxHeartbeats\b"), "heartbeat override"),
    (re.compile(r"\bset_option\s+maxRecDepth\b"), "recursion-depth override"),
]


def mask(src: str) -> str:
    """Replace comments and string literals by spaces, keeping line breaks."""
    out = list(src)
    i, n = 0, len(src)

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith("/-", i):
            start, depth = i, 0
            while i < n:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            blank(start, i)
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i, min(j + 1, n))
            i = j + 1
        else:
            i += 1
    return "".join(out)


def main() -> int:
    root = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent)
    files = sorted([root / "Riesz2.lean", *(root / "Riesz2").rglob("*.lean"),
                    *(root / "Riesz2Audit").rglob("*.lean")])
    errors = []
    for path in files:
        code = mask(path.read_text(encoding="utf-8"))
        if path.parent.parent == root / "Riesz2Audit" and path.name == "Challenge.lean":
            sorries = [m.start() for m in FORBIDDEN[0][0].finditer(code)]
            tail = code[sorries[0] + 5:] if sorries else ""
            if len(sorries) != 1 or not re.fullmatch(r"(\s*end(?:[ \t]+[\w.]+)?)*\s*", tail):
                errors.append(f"a challenge needs exactly one `sorry`, ending the file: "
                              f"{path.relative_to(root)}")
            code = code.replace("sorry", "     ")
        for pattern, what in FORBIDDEN:
            for match in pattern.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                errors.append(f"{what}: {path.relative_to(root)}:{line}")
    if errors:
        print("SOURCE CHECK FAILED:")
        for error in errors:
            print(f"- {error}")
        return 1
    print(f"SOURCE CHECK OK ({len(files)} Lean files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
