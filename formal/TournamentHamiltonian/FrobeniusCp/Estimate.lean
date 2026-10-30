module

public import TournamentHamiltonian.FrobeniusCp.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FrobeniusCp
open scoped BigOperators Matrix.Norms.Elementwise Topology
attribute [local instance] Classical.propDecidable Classical.decEq
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

lemma principalMinor_quadratic_bound (K : Matrix n n 𝕜) (hK : frobenius K ≤ 1)
    (s : Finset n) (hs : 2 ≤ s.card) :
    ‖principalMinor K s‖ ≤ s.card.factorial * frobenius K ^ 2 := by
  exact (principalMinor_bound K s).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (frobenius_nonneg K) hK hs) (Nat.cast_nonneg _))

/-- The printed finite-radius bound, for real or complex matrices, with no
invertibility, symmetry or normality hypothesis. -/
theorem determinant_remainder_bound (K : Matrix n n 𝕜) (hK : frobenius K ≤ 1) :
    ‖(1 + K).det - 1 - Matrix.trace K‖ ≤
      remainderConstant (Fintype.card n) * frobenius K ^ 2 := by
  rw [remainder_eq_principal_sum]
  calc
    _ ≤ ∑ s : Finset n with 2 ≤ s.card, ‖principalMinor K s‖ := norm_sum_le _ _
    _ ≤ ∑ s : Finset n with 2 ≤ s.card, (s.card.factorial : ℝ) * frobenius K ^ 2 := by
      exact Finset.sum_le_sum fun s hs => principalMinor_quadratic_bound K hK s
        (Finset.mem_filter.mp hs).2
    _ = _ := by rw [← Finset.sum_mul, factorial_subset_sum]

omit [DecidableEq n] in
lemma real_frobenius (K : Matrix n n ℝ) :
    frobenius K = Real.sqrt (∑ i, ∑ j, K i j ^ 2) := by
  simp [frobenius, Real.norm_eq_abs, sq_abs]

theorem real_determinant_remainder_bound (K : Matrix n n ℝ)
    (hK : Real.sqrt (∑ i, ∑ j, K i j ^ 2) ≤ 1) :
    |(1 + K).det - 1 - Matrix.trace K| ≤ remainderConstant (Fintype.card n) *
      (∑ i, ∑ j, K i j ^ 2) := by
  have h := determinant_remainder_bound K (by rwa [real_frobenius])
  simpa only [Real.norm_eq_abs, frobenius_sq, sq_abs] using h

theorem complex_determinant_remainder_bound (K : Matrix n n ℂ)
    (hK : Real.sqrt (∑ i, ∑ j, ‖K i j‖ ^ 2) ≤ 1) :
    ‖(1 + K).det - 1 - Matrix.trace K‖ ≤ remainderConstant (Fintype.card n) *
      (∑ i, ∑ j, ‖K i j‖ ^ 2) := by
  simpa only [frobenius_sq] using determinant_remainder_bound K hK

omit [DecidableEq n] in
lemma continuous_frobenius : Continuous (frobenius : Matrix n n 𝕜 → ℝ) := by
  unfold frobenius
  fun_prop

omit [DecidableEq n] in
@[simp] lemma frobenius_zero : frobenius (0 : Matrix n n 𝕜) = 0 := by
  simp [frobenius]

/-- The local O statement follows with the same explicit constant, at fixed dimension. -/
theorem determinant_remainder_isBigO :
    (fun K : Matrix n n 𝕜 => (1 + K).det - 1 - Matrix.trace K) =O[𝓝 0]
      (fun K => frobenius K ^ 2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨remainderConstant (Fintype.card n), ?_⟩
  have h : ∀ᶠ K : Matrix n n 𝕜 in 𝓝 0, frobenius K < 1 :=
    continuous_frobenius.continuousAt.eventually_lt_const (by simp)
  filter_upwards [h] with K hK
  simpa only [Real.norm_eq_abs, abs_sq] using
    determinant_remainder_bound K hK.le

end FrobeniusCp
