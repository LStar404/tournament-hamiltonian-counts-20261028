# Second reviewer revision of 11 November 2026

Base: `1b66d66cd287310c3a85dc3c64816fa319d55af2`. The first revision and its validation records remain unchanged in `review/revision-20261111/`. This revision corrects an abstract hypothesis, adds two elementary consequences of the existing stability result, and harmonizes the necessary technical appendix.

## Changes and their scope

1. **Self-contained, correctly quantified abstracts.** Both languages now define the path count, maximum, random benchmark and constant `L`, and require `0 <= epsilon <= (L-1)/2` for sufficiently large order. The omitted range was a real overstatement: with epsilon equal to L every tournament satisfies the hypothesis, while a transitive tournament has variance `n(n^2-1)/12`, not O(n^2). The already correct theorem and its proof are unchanged.
2. **The structural mechanism is stated accurately.** Section 1.2 attributes stability to the retained score penalty together with the quantitative lower bound, rather than to the numerical maximum asymptotic alone.
3. **Even-order linear scale.** The remark after Theorem 1.2 proves `V_deg >= n/4` by half-integrality of each degree deviation, with equality exactly for balanced degrees. Together with Corollary 8.3, this yields `V_deg = Theta(n)` for exact maximizers of even order. It does not claim optimal dependence on epsilon or identify the maximizers.
4. **An actual-maximum window.** New Corollary 8.4 uses `delta=(P(n)-H(T))/mu_n` and absolute constants C,N for `0 <= delta <= (L-1)/4`, `n >= N`, obtaining `V_deg <= C(delta*n^2+n)`. Its proof explicitly chooses a fixed lower-bound constant and ensures that the substituted epsilon lies in Corollary 8.3's range. A fixed `A*mu_n/n` count gap therefore gives `O_A(n)` degree variance. This is a direct consequence, not a separate novelty claim.
5. **Unified submission appendix.** Maximum score is Delta_s in both main text and appendix; the analytic majorant is G_{C,q}. Matrix order, local combinatorial degrees, the score product Gamma and the Gamma distribution remain distinct. The actual carousel example now cites A.2 and Lemma 6.1, not the old Section 8.2. Main-paper references are explicit. Local literature comparisons align with the main paper, including McCullagh's existing rate and complex perturbations. The complete independent proof remains available for its parameter tracking through cores, the finite coefficient window, restoration and tails.
6. **English formal-coverage summary.** [lean_coverage.en.md](lean_coverage.en.md) provides 37 English rows and fixed evidence links. The author statement gives a concise English scope summary and clickable commit-pinned correspondence/build links. Neither new consequence, nor the score-sensitive bound or degree stability, is represented as a newly checked Lean endpoint.

## Reproduction and validation

- `python tools/render_compact_main.py`
- `python tools/build_technical_appendix.py --check`
- `python tools/compile_tex.py --check`
- `python review/revision-20261111-round2/check_stability_examples.py`
- `python review/revision-20261111-round2/check_lean_coverage.py`

The appendix generator applies only enumerated, counted editorial transformations to frozen source blocks. It checks raw and transformed SHA-256 values, preserves equation tags and references, and rejects unexpected proof changes. Historical detailed companions and Lean production sources are not rewritten.

[stability_examples.json](stability_examples.json) records exact polynomial identities and all labelled tournaments of orders 1–5. These finite checks do not establish the general asymptotic theorem. [validation.json](validation.json) records the actual source checks, exact regressions, PDF builds and visual inspection for this revision. No full Lean compilation, new recursive axiom audit or new GitHub Actions run is claimed.

The submission pair remains the English main manuscript and necessary English technical appendix; Chinese counterparts provide parallel review copies. The longer detailed companions remain optional expanded reading. The first path-count correction, stronger structural stability and the general optimal epsilon dependence remain open.
