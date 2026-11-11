# English review package

The canonical research-submission pair is the English combined manuscript and its required English technical appendix. The Chinese versions remain synchronized reading counterparts. The package is for review preparation, not an external submission: no journal has been selected, and no journal-format compliance is claimed.

From the repository root, build and check the local archive:

```sh
python tools/package_submission.py
python tools/package_submission.py --check
```

The default output is `build/submission/english-review-pdfs.zip`. An optional `--output PATH.zip` selects another local archive. `--check` reads the current inputs and existing archive, verifies the exact safe member list and SHA-256 hashes, and writes nothing. It exits nonzero if the archive is missing, stale, or invalid. Rebuild after updating either PDF.

The explicit input allowlist contains only:

- `manuscripts/02_combined.en.pdf` → `Main-Manuscript-English.pdf`
- `manuscripts/09_technical_appendix.en.pdf` → `Technical-Appendix-English.pdf`

`MANIFEST.json` records each PDF's repository source path, byte count, and SHA-256, plus the PDF-only and non-upload scope. Fixed ZIP timestamps, stable metadata and ordering, and uncompressed entries make identical input bytes produce identical archive bytes. No build date or commit hash is embedded.

Guides, `guide_parts/`, detailed-proof companions, Chinese reading editions, and historical review/audit records are excluded. The full Markdown and TeX sources remain in the repository; this PDF-only bundle is not a journal source package. The script neither compiles PDFs nor verifies their mathematical content or visual layout, and it never uploads files.
