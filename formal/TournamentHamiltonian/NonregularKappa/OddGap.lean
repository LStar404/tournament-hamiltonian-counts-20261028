module

public import TournamentHamiltonian.NonregularKappa.LogLoss

@[expose] public section

set_option autoImplicit false
namespace NonregularKappa
open TournamentHamiltonian RegularOrientation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- For an odd-order actual tournament, each nonzero signed score has square at
least four. The parity comes from the actual integer outdegree. -/
theorem odd_score_sq_ge_four {d : ℕ} (hodd : Odd d) (T : Tournament d)
    (i : Fin d) (hi : score T i ≠ 0) : 4 ≤ score T i^2 := by
  obtain ⟨k, rfl⟩ := hodd
  have he := score_eq_outDegree T i
  push_cast at he
  have hne : outDegree T i ≠ k := by
    intro hk
    rw [hk] at he
    apply hi
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : outDegree T i+1 ≤ k := by omega
    have hR : (outDegree T i : ℝ)+1 ≤ k := by exact_mod_cast hn
    have hs : score T i ≤ -2 := by linarith
    nlinarith
  · have hn : k+1 ≤ outDegree T i := by omega
    have hR : (k : ℝ)+1 ≤ outDegree T i := by exact_mod_cast hn
    have hs : 2 ≤ score T i := by linarith
    nlinarith

/-- Zero total score forces a second nonzero score at a different vertex. -/
theorem exists_second_nonzero_score {d : ℕ} (T : Tournament d)
    (i : Fin d) (hi : score T i ≠ 0) : ∃ j, j ≠ i ∧ score T j ≠ 0 := by
  by_contra h
  have hz : ∀ j, j ≠ i → score T j = 0 := by
    intro j hji
    by_contra hj
    exact h ⟨j, hji, hj⟩
  have he : (∑ j, score T j) = score T i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hz j hji
    · simp
  rw [score_sum_zero] at he
  exact hi he.symm

/-- The manuscript's discrete gap eight for every actual odd-order nonregular base. -/
theorem odd_nonregular_score_square_sum_ge_eight {d : ℕ} (hodd : Odd d)
    (T : Tournament d) (hT : ¬IsRegular T) : 8 ≤ ∑ i, score T i^2 := by
  obtain ⟨i, hi⟩ : ∃ i, score T i ≠ 0 := by simpa [RegularOrientation.IsRegular] using hT
  obtain ⟨j, hji, hj⟩ := exists_second_nonzero_score T i hi
  have hi4 := odd_score_sq_ge_four hodd T i hi
  have hj4 := odd_score_sq_ge_four hodd T j hj
  have hs : (∑ v ∈ ({i,j} : Finset (Fin d)), score T v^2) ≤ ∑ v, score T v^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro v _ _
    exact sq_nonneg _
  simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hji.symm), Finset.sum_singleton] at hs
  linarith

theorem kappa_pow_eq_exp_log {d : ℕ} (T : Tournament d) (N : ℕ) :
    kappa T ^ N = Real.exp ((N : ℝ) * Real.log (kappa T)) := by
  rw [Real.exp_nat_mul, Real.exp_log (kappa_pos T)]

/-- Quantitative decay for any nonnegative integer exponent, with the actual
score-square penalty. This statement needs no parity or nonregularity hypothesis. -/
theorem kappa_pow_le_exp_score_loss {d : ℕ} (hd : 0 < d) (T : Tournament d) (N : ℕ) :
    kappa T ^ N ≤ Real.exp (-(N : ℝ) * (∑ i, score T i^2) / (8*(d : ℝ)^3)) := by
  rw [kappa_pow_eq_exp_log]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (log_kappa_le_score_loss hd T) (Nat.cast_nonneg N)
  convert h using 1
  ring

/-- §11.3's displayed odd nonregular exponential loss, valid even at N=0. -/
theorem odd_nonregular_kappa_pow_le {d : ℕ} (hd : 0 < d) (hodd : Odd d)
    (T : Tournament d) (hT : ¬IsRegular T) (N : ℕ) :
    kappa T ^ N ≤ Real.exp (-(N : ℝ) / (d : ℝ)^3) := by
  apply (kappa_pow_le_exp_score_loss hd T N).trans
  apply Real.exp_le_exp.mpr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap := odd_nonregular_score_square_sum_ge_eight hodd T hT
  have hmul := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg N)
  have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 8*(d : ℝ)^3)
  have he : (N : ℝ)*8 / (8*(d : ℝ)^3) = (N : ℝ)/(d : ℝ)^3 := by field_simp
  rw [he] at hdiv
  convert neg_le_neg hdiv using 1 <;> ring

end
end NonregularKappa
