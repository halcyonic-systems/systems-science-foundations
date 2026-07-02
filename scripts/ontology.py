#!/usr/bin/env python3
# ontology.py — text-level index over the SSF Lean sources (LAMP phase 1).
#
# Answers "exact statement of X / its docstring / where it lives / what it
# touches" for proof sessions. The text layer re-parses on every run (~8k
# lines, milliseconds). The `axioms` subcommand shells out to `lake env lean`
# for kernel-true answers, reusing axiom-profile.sh's scratch-file pattern.
#
# Usage:
#   python3 scripts/ontology.py lookup <name>     exact statement + docstring
#   python3 scripts/ontology.py search <term>     substring over names + docs
#   python3 scripts/ontology.py deps <name>       heuristic uses / used-by
#   python3 scripts/ontology.py module <path>     declarations in one file
#   python3 scripts/ontology.py axioms <name>     kernel-true (slow)
#   python3 scripts/ontology.py stats             counts by kind and module
#
# `deps` is an identifier-mention scan over statements, not kernel truth.
# Systems/Bunge/ is excluded unless --all (experimental, not imported).

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

KINDS = {"structure", "def", "theorem", "lemma", "abbrev", "class",
         "instance", "inductive", "opaque"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe"}
OPENERS = "([{⟨"
CLOSERS = ")]}⟩"

CITE_RE = re.compile(
    r"(?:Bunge|Mobus|Klir|Myers|Wymore|Mesarović|Mesarovic|Joslyn|Simon)"
    r"\s+(?:Def(?:inition)?|§|Principle|Ch(?:apter)?\.?)\s*[\d.]*\d")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def lean_files(include_all):
    files = [ROOT / "Systems.lean"]
    for p in sorted((ROOT / "Systems").rglob("*.lean")):
        if not include_all and "Bunge" in p.relative_to(ROOT).parts:
            continue
        files.append(p)
    return [f for f in files if f.exists()]


def module_name(rel):
    return rel[:-len(".lean")].replace("/", ".")


def consume_comment(lines, i):
    buf = [lines[i]]
    while "-/" not in buf[-1]:
        i += 1
        buf.append(lines[i])
    return buf, i + 1


def section_heading(buf):
    text = "\n".join(buf)
    text = text[text.index("/-!") + 3:]
    if "-/" in text:
        text = text[:text.index("-/")]
    for line in text.splitlines():
        line = line.strip().lstrip("#").strip()
        if line:
            return line
    return None


def strip_proof(raw):
    depth = 0
    out = []
    for line in raw:
        j = 0
        while j < len(line):
            ch = line[j]
            if ch in OPENERS:
                depth += 1
            elif ch in CLOSERS:
                depth -= 1
            elif depth == 0 and line[j:j + 2] == ":=":
                prefix = line[:j].rstrip()
                if prefix:
                    out.append(prefix)
                return out
            j += 1
        out.append(line)
    return out


def decl_name_token(tok):
    for cut in (":", "("):
        if cut in tok:
            tok = tok[:tok.index(cut)]
    return tok or None


def parse_file(path):
    rel = str(path.relative_to(ROOT))
    lines = path.read_text(encoding="utf-8").splitlines()
    decls = []
    imports = []
    ns = []
    section = None
    pending_doc = []
    pending_attrs = []
    current = None

    def finalize():
        nonlocal current
        if current is None:
            return
        raw = current.pop("raw")
        while raw and not raw[-1].strip():
            raw.pop()
        if current["kind"] in ("theorem", "lemma"):
            raw = strip_proof(raw)
        current["text"] = "\n".join(raw)
        decls.append(current)
        current = None

    i = 0
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        indent = len(line) - len(line.lstrip())

        if current is not None:
            if not s or indent > 0:
                current["raw"].append(line)
                i += 1
                continue
            finalize()

        if not s:
            i += 1
            continue
        if s.startswith("/--"):
            buf, i = consume_comment(lines, i)
            pending_doc = buf if indent == 0 else []
            continue
        if s.startswith("/-!"):
            buf, i = consume_comment(lines, i)
            section = section_heading(buf) or section
            continue
        if s.startswith("/-"):
            _, i = consume_comment(lines, i)
            continue
        if s.startswith("--"):
            i += 1
            continue
        if s.startswith("import "):
            imports.append(s.split()[1])
            i += 1
            continue
        if s.startswith("namespace "):
            ns.append(s.split()[1])
            pending_doc = []
            i += 1
            continue
        if s.startswith("end"):
            toks = s.split()
            if len(toks) > 1 and ns and ns[-1] == toks[1]:
                ns.pop()
            i += 1
            continue
        if s.startswith("@["):
            pending_attrs.append(line)
            depth = s.count("[") - s.count("]")
            while depth > 0:
                i += 1
                pending_attrs.append(lines[i])
                depth += lines[i].count("[") - lines[i].count("]")
            i += 1
            continue

        toks = s.split()
        j = 0
        while j < len(toks) and toks[j] in MODIFIERS:
            j += 1
        if j < len(toks) and toks[j] in KINDS:
            kind = toks[j]
            name = None
            if j + 1 < len(toks) and toks[j + 1][0] not in ":([{⟨|":
                name = decl_name_token(toks[j + 1])
            if name is None:
                name = f"{kind}@{i + 1}"
            doc = "\n".join(pending_doc)
            current = {
                "name": ".".join(ns + [name]),
                "short": name,
                "kind": kind,
                "file": rel,
                "line": i + 1,
                "section": section,
                "doc": doc,
                "cites": CITE_RE.findall(doc),
                "raw": pending_attrs + [line],
            }
            pending_doc = []
            pending_attrs = []
        i += 1
    finalize()
    return decls, imports


class Index:
    def __init__(self, include_all):
        self.decls = []
        self.imports = {}
        for path in lean_files(include_all):
            decls, imports = parse_file(path)
            self.decls.extend(decls)
            self.imports[module_name(str(path.relative_to(ROOT)))] = imports
        self.by_name = {d["name"]: d for d in self.decls}

    def resolve(self, name):
        if name in self.by_name:
            return self.by_name[name], []
        hits = [d for d in self.decls
                if d["name"].endswith("." + name) or d["short"] == name]
        if len(hits) == 1:
            return hits[0], []
        return None, hits


def locate(d):
    return f"{d['name']}  [{d['kind']}]  {d['file']}:{d['line']}"


def print_decl(d):
    print(locate(d))
    if d["section"]:
        print(f"section: {d['section']}")
    if d["cites"]:
        print(f"cites: {', '.join(d['cites'])}")
    if d["doc"]:
        print(d["doc"])
    print(d["text"])


def resolve_or_die(index, name):
    d, hits = index.resolve(name)
    if d:
        return d
    if hits:
        print(f"ambiguous '{name}' — candidates:", file=sys.stderr)
        for h in hits:
            print(f"  {locate(h)}", file=sys.stderr)
    else:
        print(f"not found: '{name}' (try the search subcommand)",
              file=sys.stderr)
    sys.exit(1)


def cmd_lookup(index, args):
    d = resolve_or_die(index, args.name)
    if args.json:
        print(json.dumps({k: v for k, v in d.items()}, ensure_ascii=False,
                         indent=2))
    else:
        print_decl(d)


def cmd_search(index, args):
    term = args.term.lower()
    hits = [d for d in index.decls
            if term in d["name"].lower() or term in d["doc"].lower()]
    if args.json:
        print(json.dumps([locate(d) for d in hits], ensure_ascii=False,
                         indent=2))
        return
    for d in hits:
        first = next((l.strip().lstrip("/-").strip()
                      for l in d["doc"].splitlines() if l.strip()), "")
        print(f"{locate(d)} — {first}" if first else locate(d))
    if not hits:
        print("no matches")


def mention_parts(text):
    parts = set()
    for tok in IDENT_RE.findall(text):
        parts.add(tok)
        parts.update(tok.split("."))
    return parts


def cmd_deps(index, args):
    d = resolve_or_die(index, args.name)
    parts = mention_parts(d["text"])
    uses = [o for o in index.decls
            if o is not d and (o["short"] in parts or
                               o["short"].split(".")[-1] in parts)]
    tail = d["name"].split(".")[-1]
    used_by = [o for o in index.decls
               if o is not d and tail in mention_parts(o["text"])]
    mod = module_name(d["file"])
    result = {
        "target": locate(d),
        "uses": sorted({locate(o) for o in uses}),
        "used_by": sorted({locate(o) for o in used_by}),
        "module": mod,
        "module_imports": index.imports.get(mod, []),
        "imported_by": sorted(m for m, deps in index.imports.items()
                              if mod in deps),
    }
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    print(result["target"])
    print("\nuses (heuristic identifier scan of the statement):")
    for x in result["uses"]:
        print(f"  {x}")
    print("\nused-by (statements mentioning it, heuristic):")
    for x in result["used_by"]:
        print(f"  {x}")
    print(f"\nmodule: {mod}")
    print(f"  imports: {', '.join(result['module_imports']) or '(none)'}")
    print(f"  imported by: {', '.join(result['imported_by']) or '(none)'}")


def cmd_module(index, args):
    rel = args.path
    if not rel.endswith(".lean"):
        rel = rel.replace(".", "/") + ".lean"
    hits = [d for d in index.decls if d["file"] == rel]
    if not hits:
        print(f"no declarations found in '{rel}'", file=sys.stderr)
        sys.exit(1)
    if args.json:
        print(json.dumps([locate(d) for d in hits], ensure_ascii=False,
                         indent=2))
        return
    for d in hits:
        print(f"{d['line']:5}  {d['kind']:9}  {d['name']}")


def cmd_stats(index, args):
    by_kind = {}
    by_module = {}
    for d in index.decls:
        by_kind[d["kind"]] = by_kind.get(d["kind"], 0) + 1
        by_module[d["file"]] = by_module.get(d["file"], 0) + 1
    result = {"total": len(index.decls), "by_kind": by_kind,
              "by_module": by_module}
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return
    print(f"total declarations: {result['total']}")
    print("\nby kind:")
    for k, v in sorted(by_kind.items(), key=lambda kv: -kv[1]):
        print(f"  {k:10} {v}")
    print("\nby module:")
    for m, v in sorted(by_module.items()):
        print(f"  {m:45} {v}")


def cmd_axioms(index, args):
    d = resolve_or_die(index, args.name)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as f:
        f.write(f"import Systems\n#print axioms {d['name']}\n")
        scratch = f.name
    try:
        proc = subprocess.run(["lake", "env", "lean", scratch], cwd=ROOT,
                              capture_output=True, text=True)
        out = (proc.stdout + proc.stderr).strip()
        print(out or "(no output)")
        sys.exit(proc.returncode)
    finally:
        Path(scratch).unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(
        description="Text-level index over the SSF Lean sources.")
    parser.add_argument("--all", action="store_true",
                        help="include Systems/Bunge/ (experimental)")
    parser.add_argument("--json", action="store_true")
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("lookup").add_argument("name")
    sub.add_parser("search").add_argument("term")
    sub.add_parser("deps").add_argument("name")
    sub.add_parser("module").add_argument("path")
    sub.add_parser("axioms").add_argument("name")
    sub.add_parser("stats")
    args = parser.parse_args()

    index = Index(args.all)
    {"lookup": cmd_lookup, "search": cmd_search, "deps": cmd_deps,
     "module": cmd_module, "stats": cmd_stats,
     "axioms": cmd_axioms}[args.cmd](index, args)


if __name__ == "__main__":
    main()
