module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
Finite-family limit comparison used in manuscript Appendix A.6.
The analytic limits and strict limiting gaps are explicit hypotheses;
this module does not establish Wormald's asymptotic counting theorem.
-/

public section

open Filter
open scoped Topology

namespace Tournament

/-- Young's inequality with the exact constants used in §7.4/§12.3.
Here `n` is a positive real, so the statement also applies to positive integer sizes. -/
theorem sqrt_error_absorption (K τ n : ℝ) (hτ : 0 ≤ τ) (hn : 0 < n) :
    K * Real.sqrt (τ / n) ≤ τ / 4 + K ^ 2 / n := by
  have hsτ := Real.sq_sqrt hτ
  have hsn := Real.sq_sqrt (le_of_lt hn)
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  rw [Real.sqrt_div hτ]
  have hh := sq_nonneg (Real.sqrt τ * Real.sqrt n / 2 - K)
  have hm : (Real.sqrt τ * Real.sqrt n) ^ 2 = τ * n := by
    rw [mul_pow, hsτ, hsn]
  have hcancel : (K * (Real.sqrt τ / Real.sqrt n)) * n =
      K * (Real.sqrt τ * Real.sqrt n) := by
    conv_lhs => arg 2; rw [← hsn]
    field_simp [ne_of_gt hpos]
  have hright : (τ / 4 + K ^ 2 / n) * n = τ * n / 4 + K ^ 2 := by
    field_simp [ne_of_gt hn]
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith [hh, hm, hcancel, hright]

/-- Once the non-square-root error has been controlled by τ/4 + A/n,
the score-dependent exponent has a uniform O(1/n) upper bound.
Establishing that premise on the paper's logarithmic window remains a separate step. -/
theorem total_error_absorption (K τ n A r : ℝ) (hτ : 0 ≤ τ) (hn : 0 < n)
    (hr : r ≤ τ / 4 + A / n) :
    -τ + r + K * Real.sqrt (τ / n) ≤ -τ / 2 + (A + K ^ 2) / n := by
  have h := sqrt_error_absorption K τ n hτ hn
  rw [add_div]
  linarith

/-- A strict gap between limits eventually becomes a strict gap between values.
Works for any filter, including the filter along odd block sizes. -/
theorem eventual_lt_of_limit_gap {α : Type*} {l : Filter α}
    {f g : α → ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hab : a < b) :
    ∀ᶠ x in l, f x < g x := by
  have hleft : a < (a + b) / 2 := by linarith
  have hright : (a + b) / 2 < b := by linarith
  have hf' : ∀ᶠ x in l, f x < (a + b) / 2 :=
    hf.eventually (eventually_lt_nhds hleft)
  have hg' : ∀ᶠ x in l, (a + b) / 2 < g x :=
    hg.eventually (eventually_gt_nhds hright)
  filter_upwards [hf', hg'] with x hx hy
  exact lt_trans hx hy

/-- The finite collection of comparison thresholds can be made uniform. -/
theorem finite_eventual_forall {α ι : Type*} {l : Filter α}
    (s : Finset ι) (P : ι → α → Prop)
    (h : ∀ i ∈ s, ∀ᶠ x in l, P i x) :
    ∀ᶠ x in l, ∀ i ∈ s, P i x := by
  exact (Filter.eventually_all_finset s).2 h

/-- Unique largest limiting value implies eventual unique maximization
over a finite family. The distinguished member need not belong to `s`. -/
theorem finite_eventual_unique_max {α ι : Type*} {l : Filter α}
    (s : Finset ι) (f : ι → α → ℝ) (a : ι → ℝ)
    (g : α → ℝ) (b : ℝ)
    (hf : ∀ i ∈ s, Tendsto (f i) l (𝓝 (a i)))
    (hg : Tendsto g l (𝓝 b))
    (hgap : ∀ i ∈ s, a i < b) :
    ∀ᶠ x in l, ∀ i ∈ s, f i x < g x := by
  apply finite_eventual_forall s
  intro i hi
  exact eventual_lt_of_limit_gap (hf i hi) hg (hgap i hi)

end Tournament
