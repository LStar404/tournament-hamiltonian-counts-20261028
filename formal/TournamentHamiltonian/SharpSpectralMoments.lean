module

public import TournamentHamiltonian.Packing
public import TournamentHamiltonian.SkewSpectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Odd moments control the sharp spectral product

This is the scalar analytic implication used after the Fang--Huang matrix
comparison: comparison of every odd power sum implies comparison of the
products `(1+x)/(1-x)`.  It does not prove that a tournament's moments are
dominated by the transitive tournament; that finite matrix obligation must
still be established separately.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

theorem ratio_product_pos (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1) : 0 < (xs.map ratio).prod := by
  apply List.prod_pos
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hy := hxs y hy
  unfold ratio
  exact div_pos (by linarith) (by linarith)

/-- An absolutely convergent odd-moment expansion, summed over the finite list. -/
theorem hasSum_log_ratio_product (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) *
      (xs.map (fun x => x ^ (2 * k + 1))).sum) (Real.log (xs.map ratio).prod) := by
  induction xs with
  | nil => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀ y ∈ xs, 0 ≤ y ∧ y < 1 := fun y hy => hxs y (by simp [hy])
    have hxabs : |x| < 1 := by simpa only [abs_of_nonneg hx.1] using hx.2
    have hs : HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1))
        (Real.log (ratio x)) := by
      simpa only [ratio, Real.log_div (by linarith : (1 : ℝ) + x ≠ 0)
        (by linarith : (1 : ℝ) - x ≠ 0)] using Real.hasSum_log_sub_log_of_abs_lt_one hxabs
    have hprod := ratio_product_pos xs ht
    have hr : 0 < ratio x := by unfold ratio; exact div_pos (by linarith) (by linarith)
    simpa only [List.map_cons, List.sum_cons, List.prod_cons,
      Real.log_mul hr.ne' hprod.ne', mul_add] using hs.add (ih ht)

/-- All odd moments, rather than a fixed finite collection, control the ratio. -/
theorem ratio_product_le_of_odd_moments (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hys : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmoments : ∀ k : ℕ, (xs.map (fun x => x ^ (2 * k + 1))).sum ≤
      (ys.map (fun y => y ^ (2 * k + 1))).sum) :
    (xs.map ratio).prod ≤ (ys.map ratio).prod := by
  have hxpos := ratio_product_pos xs hxs
  have hypos := ratio_product_pos ys hys
  apply (Real.log_le_log_iff hxpos hypos).mp
  apply hasSum_le _ (hasSum_log_ratio_product xs hxs) (hasSum_log_ratio_product ys hys)
  intro k
  exact mul_le_mul_of_nonneg_left (hmoments k) (by positivity)

/-- Instantiation for the actual paired frequencies of two tournaments.
The displayed odd-moment comparison is an explicit intermediate premise. -/
theorem spectralRatio_le_of_odd_paired_moments {n : ℕ} (T U : Tournament n) (hn : 0 < n)
    (hmoments : ∀ k : ℕ, ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum ≤
      ((pairedMasses U).map (fun x => x ^ (2 * k + 1))).sum) :
    spectralRatio T ≤ spectralRatio U := by
  rw [spectralRatio_eq_paired_product T hn, spectralRatio_eq_paired_product U hn]
  apply ratio_product_le_of_odd_moments _ _ _ _ hmoments
  · intro x hx
    exact ⟨pairedMasses_nonneg T x hx, (pairedMasses_lt_half T hn x hx).trans (by norm_num)⟩
  · intro x hx
    exact ⟨pairedMasses_nonneg U x hx, (pairedMasses_lt_half U hn x hx).trans (by norm_num)⟩

/-- The exact spectral target is the transitive ratio, at both parities. -/
theorem alternating_spectralRatio_eq_transitive (n : ℕ) (hn : 0 < n) :
    (spectralRatio (alternatingTournament n) : ℂ) = transitiveRatio n := by
  rw [← determinantRatio_eq_spectralRatio _ hn, determinantRatio_alternatingTournament]

/-- A quantitative, all-order estimate for the comparison factor, with no
unproved matrix comparison included as an assumption. -/
theorem alternating_spectralRatio_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |spectralRatio (alternatingTournament n) - lowerConstant| ≤ C / n := by
  obtain ⟨C, hC, N, hN, hbound⟩ := determinantRatio_alternatingTournament_error_bound
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn
  have h := hbound n hn
  rw [determinantRatio_eq_spectralRatio _ (by omega)] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

end TournamentHamiltonian
