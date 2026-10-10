#!/usr/bin/env python3
"""Check Lean's axiom reports for the main theorems listed in formalization.yaml."""

import re
import subprocess
import sys
from pathlib import Path


import runpy
ROOT = Path(__file__).resolve().parents[2]
parse_yaml = runpy.run_path(str(ROOT / "scripts/check_palomar.py"))["minimal_yaml"]
RESULTS = parse_yaml((ROOT / "formalization.yaml").read_text())["status"]["main_results"]
THEOREMS = tuple(r["declaration"] for r in RESULTS)
MODULES = tuple(dict.fromkeys(r["file"][:-5].replace("/", ".") for r in RESULTS))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    root = Path(__file__).resolve().parents[2]
    source = "".join(f"import {module}\n" for module in MODULES) + "".join(
        f"#print axioms {name}\n" for name in THEOREMS
    )
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        input=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        cwd=root,
        check=False,
    )
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    reports = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
        name, axioms = match.groups()
        if name in reports:
            print(f"FAIL {name}: duplicate axiom report")
            return 1
        reports[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", result.stdout):
        name = match.group(1)
        if name in reports:
            print(f"FAIL {name}: duplicate axiom report")
            return 1
        reports[name] = set()
    failed = set(reports) != set(THEOREMS)
    if failed:
        print(f"FAIL missing reports: {sorted(set(THEOREMS) - set(reports))}")
        print(f"FAIL unexpected reports: {sorted(set(reports) - set(THEOREMS))}")
    for name in THEOREMS:
        if name in reports and not reports[name] <= ALLOWED:
            print(f"FAIL {name}: unexpected axioms {sorted(reports[name] - ALLOWED)}")
            failed = True
    if not failed:
        print(f"PASS: all {len(THEOREMS)} theorems use only the permitted standard axioms")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
