#!/usr/bin/env python3
"""Check manuscript-result coverage separately from the partial Lean build."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
CATALOG = ROOT / "paper-coverage.json"
RESULT = re.compile(
    r"\\begin\{(theorem|lemma|lemmafiveonea|proposition|corollary|fact)\}"
    r"(?:\[([^\n]*)\])?\s*\\label\{([^}]+)\}"
)
STATUSES = {"open", "statement_only", "partial", "proved"}


def manuscript_source_hashes():
    paths = list(REPO.glob("*.tex")) + list((REPO / "sections").glob("*.tex"))
    return {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def manuscript_results():
    found = {}
    for path in sorted((REPO / "sections").glob("*.tex")):
        text = path.read_text()
        for match in RESULT.finditer(text):
            kind, title, label = match.groups()
            end_token = "\\end{" + kind + "}"
            end = text.index(end_token, match.end()) + len(end_token)
            statement = text[match.start():end]
            if label in found:
                raise ValueError("duplicate manuscript result: " + label)
            found[label] = {
                "label": label,
                "kind": kind,
                "title": title or label,
                "source": str(path.relative_to(REPO)),
                "line": text.count("\n", 0, match.start()) + 1,
                "statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
            }
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    actual = manuscript_results()
    catalog = json.loads(CATALOG.read_text())
    if catalog.get("source_files") != manuscript_source_hashes():
        raise ValueError("manuscript source changed; review the definitions and proof mappings")
    recorded = {item["label"]: item for item in catalog["results"]}
    if len(recorded) != len(catalog["results"]) or recorded.keys() != actual.keys():
        raise ValueError("coverage catalog does not match all manuscript result labels")
    for label, item in recorded.items():
        for key in ("source", "kind", "statement_sha256"):
            if item[key] != actual[label][key]:
                raise ValueError(f"{label}: source statement changed; review its mapping")
        if item["status"] not in STATUSES:
            raise ValueError(f"{label}: invalid status")
        if item["status"] == "proved" and not all(
            item.get(key) for key in ("statement_declaration", "proof_declaration")
        ):
            raise ValueError(f"{label}: proved status requires a target proposition and its proof")
        for declaration in item.get("supporting_declarations", []):
            if not re.fullmatch(r"CircularLaw\.[A-Za-z0-9_'.]+", declaration):
                raise ValueError(f"{label}: invalid Lean declaration name")
    proved = sum(item["status"] == "proved" for item in recorded.values())
    print(f"Full manuscript results proved: {proved}/{len(actual)}")
    for status in ("partial", "statement_only", "open"):
        count = sum(item["status"] == status for item in recorded.values())
        print(f"{status}: {count}")
    # Resolve every claimed supporting declaration in the compiled Lean project.
    # The build and axiom audit are separate required checks.
    lines = ["import CircularLaw"]
    checked_declarations = set()

    def check_declaration(declaration):
        if declaration not in checked_declarations:
            lines.append("#check " + declaration)
            checked_declarations.add(declaration)

    for item in recorded.values():
        for declaration in item.get("supporting_declarations", []):
            check_declaration(declaration)
        for key in ("statement_declaration", "proof_declaration"):
            declaration = item.get(key)
            if declaration:
                if not re.fullmatch(r"CircularLaw\.[A-Za-z0-9_'.]+", declaration):
                    raise ValueError("invalid " + key)
                check_declaration(declaration)
        if item["status"] == "proved":
            lines.append("example : " + item["statement_declaration"] + " := " +
                         item["proof_declaration"])
    with tempfile.TemporaryDirectory(prefix="circular-law-coverage-") as temporary:
        proof_check = Path(temporary) / "Coverage.lean"
        proof_check.write_text("\n".join(lines) + "\n")
        # The growing ledger needs a larger elaboration/pretty-printing stack.
        # This changes capacity only; all declaration and proof checks remain.
        result = subprocess.run(["lake", "env", "lean", "-s", "65536", str(proof_check)], cwd=ROOT,
                                text=True, capture_output=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            return 1
    if args.require_complete and proved != len(actual):
        print("Full-paper verification is incomplete.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
