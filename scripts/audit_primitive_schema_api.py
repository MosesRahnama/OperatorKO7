from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
PRIMITIVE_ROOT = REPO_ROOT / "OperatorKO7" / "PrimitiveSchemaAPI.lean"


FORBIDDEN_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("Trace", re.compile(r"\bTrace\b")),
    ("ko7Schema", re.compile(r"\bko7Schema\b")),
    ("ko7System", re.compile(r"\bko7System\b")),
    ("RecCore", re.compile(r"\bRecCore\b")),
    ("WitnessOrder", re.compile(r"\bWitnessOrder\b")),
    ("SafeStep", re.compile(r"\bSafeStep\b")),
    ("StepCtxFull", re.compile(r"\bStepCtxFull\b")),
    ("PolyInterpretation_FullStep", re.compile(r"\bPolyInterpretation_FullStep\b")),
    ("MPO_FullStep", re.compile(r"\bMPO_FullStep\b")),
    ("ContextClosed_SN_Full", re.compile(r"\bContextClosed_SN_Full\b")),
    ("TTT2_CertificateReplay", re.compile(r"\bTTT2_CertificateReplay\b")),
]


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.MULTILINE)


@dataclass(frozen=True)
class Violation:
    path: Path
    token: str
    line: int
    snippet: str


def module_to_path(module: str) -> Path | None:
    if not module.startswith("OperatorKO7."):
        return None
    rel = Path(*module.split("."))
    return (REPO_ROOT / rel).with_suffix(".lean")


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append(" ")
                i += 2
                continue
            if ch == "\"":
                in_string = False
            out.append(" " if ch != "\n" else "\n")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend([" ", " "])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend([" ", " "])
                i += 2
                continue
            out.append(" " if ch != "\n" else "\n")
            i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.extend([" ", " "])
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend([" ", " "])
            i += 2
            continue
        if ch == "\"":
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def import_closure(root: Path) -> list[Path]:
    visited: set[Path] = set()
    order: list[Path] = []

    def visit(path: Path) -> None:
        path = path.resolve()
        if path in visited:
            return
        visited.add(path)
        order.append(path)
        text = path.read_text(encoding="utf-8")
        for mod in IMPORT_RE.findall(text):
            dep = module_to_path(mod)
            if dep is not None and dep.exists():
                visit(dep)

    visit(root)
    return order


def line_number(text: str, index: int) -> int:
    return text.count("\n", 0, index) + 1


def line_at(text: str, line: int) -> str:
    lines = text.splitlines()
    if 1 <= line <= len(lines):
        return lines[line - 1].strip()
    return ""


def audit_files(paths: list[Path]) -> list[Violation]:
    violations: list[Violation] = []
    for path in paths:
        raw = path.read_text(encoding="utf-8")
        code = strip_lean_comments_and_strings(raw)
        for token, pattern in FORBIDDEN_PATTERNS:
            for match in pattern.finditer(code):
                line = line_number(code, match.start())
                violations.append(
                    Violation(
                        path=path,
                        token=token,
                        line=line,
                        snippet=line_at(raw, line),
                    )
                )
    return violations


def main() -> int:
    closure = import_closure(PRIMITIVE_ROOT)
    violations = audit_files(closure)

    print(f"Primitive root: {PRIMITIVE_ROOT}")
    print(f"Files in import closure: {len(closure)}")
    for path in closure:
        print(f"  - {path.relative_to(REPO_ROOT)}")

    if not violations:
        print("\nAudit result: PASS")
        print("No forbidden KO7-facing tokens were found in code outside comments/strings.")
        return 0

    print("\nAudit result: FAIL")
    for v in violations:
        rel = v.path.relative_to(REPO_ROOT)
        print(f"{rel}:{v.line}: forbidden token `{v.token}`")
        if v.snippet:
            safe = v.snippet.encode("ascii", errors="backslashreplace").decode("ascii")
            print(f"    {safe}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
