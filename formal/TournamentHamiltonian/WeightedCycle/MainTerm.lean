module

public import TournamentHamiltonian.PrincipalGenerating
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

namespace WeightedCycle
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open TournamentHamiltonian
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The projection onto constants. Here `J` means all ones, not the identity. -/
def constantProjection : Matrix α α ℝ :=
  Matrix.of fun _ _ => (Fintype.card α : ℝ)⁻¹

def centered (D : Matrix α α ℝ) : Matrix α α ℝ := D - constantProjection


omit [DecidableEq α] in
/-- Centering removes the row-constant direction; no positivity is used. -/
theorem centered_mul_constantProjection [Nonempty α] (D : Matrix α α ℝ)
    (hrow : ∀ i, ∑ j, D i j = 1) :
    centered D * constantProjection = 0 := by
  ext i j
  simp only [Matrix.mul_apply, centered, Matrix.sub_apply, constantProjection,
    Matrix.of_apply, Matrix.zero_apply, sub_mul, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hrow, one_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

omit [DecidableEq α] in
/-- The dual annihilation follows from actual column sums. -/
theorem constantProjection_mul_centered [Nonempty α] (D : Matrix α α ℝ)
    (hcol : ∀ j, ∑ i, D i j = 1) :
    constantProjection * centered D = 0 := by
  ext i j
  simp only [Matrix.mul_apply, centered, Matrix.sub_apply, constantProjection,
    Matrix.of_apply, Matrix.zero_apply, mul_sub, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hcol, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

omit [DecidableEq α] in
theorem constantProjection_eq_normalized_ones :
    (constantProjection : Matrix α α ℝ) =
      (Fintype.card α : ℝ)⁻¹ • Matrix.of (fun _ _ : α => (1 : ℝ)) := by
  ext i j
  simp [constantProjection]

/-- The determinant on the constant direction is `1 - t`. -/
theorem det_one_sub_smul_constantProjection [Nonempty α] (t : ℝ) :
    (1 - t • (constantProjection : Matrix α α ℝ)).det = 1 - t := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmat : (1 - t • (constantProjection : Matrix α α ℝ)) =
      1 + Matrix.replicateCol Unit (fun _ : α => -t * (Fintype.card α : ℝ)⁻¹) *
        Matrix.replicateRow Unit (fun _ : α => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply, constantProjection, sub_eq_add_neg]
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Exact factorization; even column stochasticity is unnecessary. -/
theorem det_one_sub_smul_factor [Nonempty α] (D : Matrix α α ℝ)
    (hrow : ∀ i, ∑ j, D i j = 1) (t : ℝ) :
    (1 - t • D).det = (1 - t) * (1 - t • centered D).det := by
  have hmul : (1 - t • centered D) * (1 - t • constantProjection) =
      (1 : Matrix α α ℝ) - t • D := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, centered_mul_constantProjection D hrow, smul_zero]
    simp only [centered, smul_sub]
    abel
  rw [← hmul, Matrix.det_mul, det_one_sub_smul_constantProjection]
  exact mul_comm _ _

/-- Differentiate the actual finite principal-minor expansion. -/
theorem hasDerivAt_det_one_sub_smul (M : Matrix α α ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t • M).det)
      (∑ U : Finset α, ((U.card : ℝ) * x ^ (U.card - 1)) *
        ((-M).submatrix (Subtype.val : U → α) Subtype.val).det) x := by
  classical
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Finset α)))
    (fun U _ => (hasDerivAt_pow U.card x).mul_const
      ((-M).submatrix (Subtype.val : U → α) Subtype.val).det)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  simpa only [smul_neg, sub_eq_add_neg] using matrix_principal_generating_det (-M) t

/-- The finite cycle main term, valid for every real row-stochastic matrix.
No nonnegativity, invertibility, column-sum, or spectral-gap premise occurs. -/
theorem cycle_main_term_eq_centered_det [Nonempty α] (D : Matrix α α ℝ)
    (hrow : ∀ i, ∑ j, D i j = 1) :
    -(∑ U : Finset α, (U.card : ℝ) *
      ((-D).submatrix (Subtype.val : U → α) Subtype.val).det) =
      (1 - centered D).det := by
  classical
  have hleft := hasDerivAt_det_one_sub_smul D 1
  have hcenter := hasDerivAt_det_one_sub_smul (centered D) 1
  have hlinear : HasDerivAt (fun t : ℝ => 1 - t) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_sub (1 : ℝ)
  have hright := hlinear.mul hcenter
  have heq : (fun t : ℝ => (1 - t) * (1 - t • centered D).det) =
      (fun t : ℝ => (1 - t • D).det) := by
    funext t
    exact (det_one_sub_smul_factor D hrow t).symm
  change HasDerivAt (fun t : ℝ => (1 - t) * (1 - t • centered D).det) _ _ at hright
  rw [heq] at hright
  have h := hleft.unique hright
  simp only [one_pow, mul_one, one_smul, sub_self, zero_mul, add_zero,
    neg_one_mul] at h
  exact (neg_eq_iff_eq_neg.mpr h)

/-- Manuscript notation: `J` is all ones, hence `J/N` is the constant projection. -/
theorem cycle_main_term_eq_det_one_sub_centered [Nonempty α] (D : Matrix α α ℝ)
    (hrow : ∀ i, ∑ j, D i j = 1) :
    -(∑ U : Finset α, (U.card : ℝ) *
      ((-D).submatrix (Subtype.val : U → α) Subtype.val).det) =
      (1 - (D - (Fintype.card α : ℝ)⁻¹ •
        Matrix.of (fun _ _ : α => (1 : ℝ)))).det := by
  simpa only [centered, constantProjection_eq_normalized_ones] using
    cycle_main_term_eq_centered_det D hrow

end
end WeightedCycle
