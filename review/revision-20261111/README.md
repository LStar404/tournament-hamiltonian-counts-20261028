# Revision of 11 November 2026

Base: `4af732650d7d5724bcab60a80a711d4294d58e2d`. This is an editorial and proof-organization revision. The Lean production sources are unchanged. It does not claim a new mathematical result beyond the statements already present in the base manuscript.

## Changes made

1. **Counting and degree stability are the main results.** The title, abstract and introduction now center on the global normalized `O(1/n)` path bound and the degree-variance bound. New introductory Theorem 1.2 restates the former Corollary 8.2a, now Corollary 8.3. The introduction includes the score-penalty estimate, square-root absorption and the role of summable deletion-size moments. It retains the distinction between path near-extremality here and the cycle-benchmark hypothesis in Divoux–Wang.
2. **The permanent theorem is positioned as a tool with an independent proof.** Section 3 compares fixed entry bounds with weak boundedness, identifies the determinant factors, and explains why sequence-wise versus class-uniform language is not by itself a novelty distinction. McCullagh's existing `O(1/n)` assertion and discussion of complex perturbations, and Divoux–Wang's explicit uniformity, are acknowledged. No unverified flaw in an earlier proof is alleged.
3. **Submission and reading material are separated.** The English main text and English technical appendix form the submission pair; the Chinese pair is a translation for review. The technical appendix preserves the necessary permanent, scaling and spectral-equality proofs. The older full proof companions and guides remain expanded reading. Main-text proof references point to the necessary appendix; optional high-order expansions and elementary calculations are marked as such. Duplicate baseline calculations and the repeated all-order spectral comparison are shortened.
4. **Formal coverage is explicit.** The new correspondence table records manuscript statements, exact Lean declarations, source identities and historical build evidence, with distinct statuses for an earlier proof of the same conclusion, an unmapped written proof and no new endpoint. It does not transfer old statement numbers or historical build results to new claims.
5. **Notation and presentation.** Maximum score is `Delta_s`, distinct from base order `d`; the permanent analytic majorant is `mathcal G_{C,q}`, distinct from the degree product `Gamma`. Temporary theorem suffixes 5.1a and 8.2a become 5.2 and 8.3. Other inherited numbering is retained with an explicit correspondence. Personal acknowledgments retain their recipients and significance in a more concise journal register.

## Reading and reproduction

- Main text: `manuscripts/02_combined.en.md` and `.tex` / `.pdf`.
- Technical appendix: `manuscripts/09_technical_appendix.en.md` and `.tex` / `.pdf`.
- Chinese counterparts: `01_combined.zh` and `10_technical_appendix.zh`.
- Formal correspondence: [lean_correspondence.md](lean_correspondence.md), with a machine-readable index and checker.
- This revision's validation summary: [validation.json](validation.json).

The appendix extractor records source and copy hashes. Its only transcription normalization appends an empty group after a line-ending TeX control space, preserving the control space and the proof content while avoiding trailing whitespace.

Use `python tools/render_compact_main.py` to synchronize the main TeX bodies from Markdown. Use `python tools/build_technical_appendix.py` to reproduce the selected appendix from the preserved detailed companions. Compile the four current documents using the existing `tools/compile_tex.py` or the documented portable-font builder `tools/compile_portable_pdfs.py`. See the root README for font and engine requirements.

## Boundaries and remaining research

The bounded mean square degree deviation of exact maximizers does not imply eventual regularity, carousel uniqueness, edit-distance stability or the small-score `o(sqrt(n))` hypothesis. The spectral coefficient `-L/n` is not identified as the first correction for actual path counts. Optimal error order, the first path-count correction, stronger structural results and thresholds uniform in growing base order remain research questions, not repaired proof gaps.

No new Lean endpoint for degree stability or for the revised score-sensitive proof chain is added. No new full Lean compilation or recursive axiom audit was run for this editorial revision. Source/manifest checks and finite exact regressions are supplementary checks, not substitutes for the general proofs. Historical records and their hashes are left unchanged.
