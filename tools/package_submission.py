#!/usr/bin/env python3
"""Build or check a deterministic, local-only English review PDF archive."""

import argparse
import hashlib
import io
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "build/submission/english-review-pdfs.zip"
# This is the complete inclusion list. Never discover archive inputs by globbing.
INPUTS = (
    ("manuscripts/02_combined.en.pdf", "Main-Manuscript-English.pdf"),
    ("manuscripts/09_technical_appendix.en.pdf", "Technical-Appendix-English.pdf"),
)
FIXED_TIME = (1980, 1, 1, 0, 0, 0)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def archive_contents():
    entries = []
    records = []
    for source, name in INPUTS:
        path = ROOT / source
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing or non-regular input: {source}")
        data = path.read_bytes()
        if not data.startswith(b"%PDF-"):
            raise ValueError(f"Input does not have a PDF header: {source}")
        entries.append((name, data))
        records.append({"archive_name": name, "source_path": source,
                        "bytes": len(data), "sha256": sha256(data)})
    manifest = {
        "schema_version": 1,
        "package_type": "PDF-only English research review package",
        "delivery": "non-upload: local archive only; no external submission performed",
        "journal_format_compliance": "not assessed; no journal selected",
        "files": records,
    }
    entries.append(("MANIFEST.json", (json.dumps(manifest, indent=2, sort_keys=True)
                                       + "\n").encode("utf-8")))
    return entries


def build_bytes(entries):
    buffer = io.BytesIO()
    # Stored entries avoid compression-library version differences.
    with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_STORED) as archive:
        for name, data in entries:
            info = zipfile.ZipInfo(name, date_time=FIXED_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, data)
    return buffer.getvalue()


def check_archive(path, entries, expected):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Archive missing or non-regular: {path}; run without --check to build it")
    actual = path.read_bytes()
    with zipfile.ZipFile(io.BytesIO(actual), "r") as archive:
        infos = archive.infolist()
        if [info.filename for info in infos] != [name for name, _ in entries]:
            raise ValueError("Archive members differ from the exact allowlist (including order)")
        for info, (name, data) in zip(infos, entries):
            if (info.is_dir() or info.flag_bits & 1
                    or info.file_size != len(data)
                    or info.compress_type != zipfile.ZIP_STORED):
                raise ValueError(f"Unsafe or unexpected archive member: {name}")
            if sha256(archive.read(info)) != sha256(data):
                raise ValueError(f"Archive content/hash mismatch: {name}")
    if actual != expected:
        raise ValueError("Archive metadata or bytes differ from the deterministic package")
    return sha256(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="verify current inputs and existing archive without writing anything")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT,
                        help="local ZIP path (default: build/submission/english-review-pdfs.zip)")
    args = parser.parse_args()
    try:
        output = args.output.absolute()
        if output.suffix.lower() != ".zip" or output.is_symlink():
            raise ValueError("Output must be a non-symlink .zip path")
        entries = archive_contents()
        expected = build_bytes(entries)
        if not args.check:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(expected)
        digest = check_archive(output, entries, expected)
    except (OSError, ValueError, zipfile.BadZipFile, RuntimeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    print(f"{'Verified' if args.check else 'Built and verified'}: {output}")
    print(f"SHA256: {digest}")
    print("PDF-only; local archive; no upload or external submission.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
