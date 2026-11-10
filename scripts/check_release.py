#!/usr/bin/env python3
"""Check the publication file inventory, hashes, imports and packaged paper.

Use --write-manifest after intentional release changes. The file policy and
privacy checks run before either writing or checking the manifest.
"""

from pathlib import Path, PurePosixPath
import argparse
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "release-manifest.json"
ROOT_FILES = {
    ".gitattributes", ".gitignore", "README.md", "LICENSE", "NOTICE", "CITATION.cff", "Makefile",
    "scripts/check_release.py",
}
LEAN_FILES = {
    "README.md", "TRUST_MAP.md", "NOTICES.md", "LICENSE.openai",
    "Sarkozy.lean", "Audit.lean", "ExportNames.lean", "lakefile.lean",
    "lean-toolchain", "lake-manifest.json", "verification.json",
}
PAPER_FILES = {
    "README.md", "PUBLICATION.md", "build.py", "package_publication.py", "submission.py",
    "main.pdf", "figures/dependency_graph.pdf", "hexagon-source.zip",
    "build_record.json", "publication_manifest.json", "hexagon-standalone.tex",
    "hexagon-standalone.pdf",
}
IGNORED_DIRS = {".git", "__pycache__", ".venv", "_build"}
PRIVACY_PATTERNS = {
    "absolute home path": re.compile(r"/(?:home|Users|root)/[A-Za-z0-9_.-]+/"),
    "cloud instance address": re.compile(r"\b[\w.-]+\.(?:internal|c\.compute)\b"),
    "private key": re.compile(r"-----BEGIN (?:[A-Z]+ )?PRIVATE KEY-----"),
    "GitHub token": re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,})\b"),
    "cloud access key": re.compile(r"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b"),
    "credential-bearing URL": re.compile(r"https?://[^\s/:@]+:[^\s/@]+@"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def run(*args):
    return subprocess.check_output(args, text=True, errors="replace")


def paper_inputs():
    spec = importlib.util.spec_from_file_location("paper_build", ROOT / "paper/build.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return {p.relative_to(ROOT).as_posix() for p in module.closure()}


def public_files():
    found = {}
    for directory, dirs, files in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        dirs[:] = sorted(d for d in dirs if d not in IGNORED_DIRS
                         and base / d != ROOT / "lean/.lake")
        for name in dirs:
            require(not (base / name).is_symlink(), "Symlink directory in release")
        for name in sorted(files):
            path = base / name
            relative = path.relative_to(ROOT).as_posix()
            if relative in {".git", "release-manifest.json"}:
                continue
            require(not path.is_symlink(), f"Symlink in release: {relative}")
            require(path.is_file(), f"Non-regular release file: {relative}")
            found[relative] = path
    return found


def privacy_check(name, text):
    for label, pattern in PRIVACY_PATTERNS.items():
        require(not pattern.search(text), f"Privacy check: {label} in {name}")


def check_pdf(path):
    info = run("pdfinfo", str(path))
    privacy_check(path.name + " metadata", info + run("pdfinfo", "-meta", str(path)))
    privacy_check(path.name + " links", run("pdfinfo", "-url", str(path)))
    privacy_check(path.name + " text", run("pdftotext", str(path), "-"))
    require(re.search(r"^JavaScript:\s+no$", info, re.M), "PDF contains JavaScript")
    attachments = run("pdfdetach", "-list", str(path))
    require(attachments.startswith("0 embedded files"), "PDF contains embedded files")
    return int(re.search(r"^Pages:\s+(\d+)$", info, re.M).group(1))


def check_lean_imports(files):
    modules = {
        name[len("lean/"):-len(".lean")].replace("/", ".")
        for name in files if name.startswith("lean/") and name.endswith(".lean")
    }
    for name, path in files.items():
        if not name.startswith("lean/") or path.suffix != ".lean":
            continue
        for imported in re.findall(
                r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(Sarkozy(?:\.[\w]+)*)\s*$",
                path.read_text(), re.M):
            require(imported in modules, f"Missing Lean import {imported} in {name}")
    return len([m for m in modules if m.startswith("Sarkozy.")])


def check_links(files):
    for name, path in files.items():
        if path.suffix != ".md":
            continue
        for link in re.findall(r"\[[^\]]*\]\(([^)]+)\)", path.read_text()):
            if re.match(r"[A-Za-z]+:", link) or link.startswith("#"):
                continue
            target = (path.parent / link.split("#", 1)[0]).resolve()
            require(target.is_relative_to(ROOT) and (target.exists() or target == MANIFEST),
                    f"Broken or external local link in {name}: {link}")


def check_git_inventory(files):
    if not (ROOT / ".git").exists():
        return
    tracked = run("git", "-C", str(ROOT), "ls-files", "-z").split("\0")
    allowed = set(files) | {"release-manifest.json"}
    require(all(not name or name in allowed for name in tracked),
            "Git tracks a file outside the publication inventory")


def check_archive(closure):
    publication = json.loads((ROOT / "paper/publication_manifest.json").read_text())
    archive = ROOT / "paper/hexagon-source.zip"
    require(digest(archive.read_bytes()) == publication["archive_sha256"],
            "TeX archive hash differs from publication manifest")
    expected = {n.removeprefix("paper/") for n in closure}
    expected.add("figures/dependency_graph.pdf")
    require(set(publication["files_sha256"]) == expected,
            "Publication manifest differs from TeX source closure")
    with zipfile.ZipFile(archive) as bundle:
        require(bundle.testzip() is None, "Corrupt TeX archive")
        names = bundle.namelist()
        require(len(names) == len(set(names)) and set(names) == expected,
                "Unexpected or duplicate TeX archive members")
        require(not bundle.comment, "Unexpected TeX archive comment")
        for entry in bundle.infolist():
            name = entry.filename
            p = PurePosixPath(name)
            require(not p.is_absolute() and ".." not in p.parts and "\\" not in name,
                    "Unsafe TeX archive member")
            require(not stat.S_ISLNK(entry.external_attr >> 16), "Archive symlink")
            require(not entry.comment and not entry.extra, "Unexpected archive metadata")
            raw = bundle.read(name)
            require(raw == (ROOT / "paper" / name).read_bytes(),
                    f"Archive source differs from paper/{name}")
            require(digest(raw) == publication["files_sha256"][name],
                    f"Archive member hash mismatch: {name}")
    require(digest((ROOT / "paper/main.pdf").read_bytes()) == publication["pdf_sha256"],
            "PDF hash differs from publication manifest")
    require(digest((ROOT / "paper/package_publication.py").read_bytes())
            == publication["package_script_sha256"], "Packaging script changed")
    record = json.loads((ROOT / "paper/build_record.json").read_text())
    require(set(record["closure"]) == closure, "Build receipt source closure differs")
    for name, expected_hash in record["closure"].items():
        require(digest((ROOT / name).read_bytes()) == expected_hash,
                f"Source differs from build receipt: {name}")
    require(record["pdf_sha256"] == publication["pdf_sha256"], "Build PDF hash differs")
    require(record["pdf_version"] == "1.4", "Manuscript PDF compatibility setting changed")
    require(not record["warnings"]["package_warnings"]
            and record["warnings"]["overfull_boxes"] == 0,
            "Manuscript has unresolved package warnings or overfull boxes")
    standalone = publication["standalone_upload"]
    require(standalone["source"] == "hexagon-standalone.tex", "Unexpected standalone source")
    raw = (ROOT / "paper/hexagon-standalone.tex").read_bytes()
    require(digest(raw) == standalone["sha256"] and len(raw) == standalone["bytes"],
            "Standalone source differs from the verified export")
    require(digest((ROOT / "paper/submission.py").read_bytes())
            == standalone["export_script_sha256"], "Submission exporter changed")
    require(standalone["pdf"] == "hexagon-standalone.pdf", "Unexpected submission PDF")
    raw_pdf = (ROOT / "paper/hexagon-standalone.pdf").read_bytes()
    require(digest(raw_pdf) == standalone["pdf_sha256"] and len(raw_pdf) == standalone["pdf_bytes"],
            "Submission PDF differs from the verified artifact")
    require(not standalone["qpdf_syntax_issues"] and standalone["annotations"] == 0
            and not standalone["outlines_present"], "Submission PDF profile check failed")
    require(standalone["pages"] == publication["pages"], "Standalone page count differs")
    require(standalone["pdf_version"] == record["pdf_version"], "Standalone PDF version differs")
    require(standalone["warnings"] == record["warnings"], "Standalone warning audit differs")
    require(all(standalone["verification"][key] for key in
                ("clean_final_log", "identical_text_ignoring_whitespace", "identical_labels_and_citations")),
            "Standalone compilation or manuscript equivalence check failed")
    for audit in (record["structured_text"], publication["upload_verification"]["structured_text"],
                  standalone["verification"]["structured_text"]):
        require(audit["valid_xml"] and audit["pages"] == publication["pages"]
                and audit["words"] > 0, "PDF structured-text validation failed")
    return publication


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    closure = paper_inputs()
    fixed = ROOT_FILES | {"lean/" + n for n in LEAN_FILES}
    fixed |= {"paper/" + n for n in PAPER_FILES} | closure
    files = public_files()
    require(fixed <= set(files), "Required release files are missing: "
            + ", ".join(sorted(fixed - set(files))))
    for name, path in files.items():
        require(name in fixed or (name.startswith("lean/Sarkozy/") and name.endswith(".lean")),
                f"File is outside the publication allowlist: {name}")
        if path.suffix not in {".pdf", ".zip"}:
            privacy_check(name, path.read_text())
    publication = check_archive(closure)
    pages = check_pdf(ROOT / "paper/main.pdf")
    check_pdf(ROOT / "paper/figures/dependency_graph.pdf")
    require(check_pdf(ROOT / "paper/hexagon-standalone.pdf") == pages,
            "Submission candidate page count differs from the manuscript")
    require(pages == publication["pages"], "PDF page count differs from manifest")
    modules = check_lean_imports(files)
    check_links(files)
    check_git_inventory(files)
    manifest = {
        "format": 1,
        "paper_pages": pages,
        "lean_modules": modules,
        "lean_toolchain": (ROOT / "lean/lean-toolchain").read_text().strip(),
        "files": {name: {"sha256": digest(path.read_bytes()), "bytes": path.stat().st_size}
                  for name, path in sorted(files.items())},
    }
    if args.write_manifest:
        MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
    else:
        require(MANIFEST.is_file(), "Run make manifest to create the release inventory")
        recorded = json.loads(MANIFEST.read_text())
        require(recorded == manifest, "Release inventory or hashes changed; review changes "
                "before running make manifest")
    print(f"PASS: {len(files)} release files, {pages} paper pages, {modules} Lean modules; "
          "hashes, imports, links, PDF content/metadata and TeX archive checked.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError, KeyError) as error:
        print(f"release check failed: {error}", file=sys.stderr)
        sys.exit(1)
