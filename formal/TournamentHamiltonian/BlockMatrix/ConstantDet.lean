module

public import TournamentHamiltonian.BlockMatrix.Core
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
@[expose] public section
open scoped BigOperators

namespace UniformBlockMatrix
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A constant row sum is an exact right-eigenvector identity for the all-ones matrix. -/
theorem mul_ones_of_row_sum (A : Matrix ι ι ℝ) (c : ℝ)
    (hrow : ∀ i, ∑ j, A i j = c) : A * ones ι = c • ones ι := by
  ext i j
  simpa [Matrix.mul_apply, ones] using hrow i

/-- The all-ones perturbation of identity has only one nontrivial determinant factor.
This includes the empty index type, where the determinant and the RHS are both one. -/
theorem det_one_add_smul_ones (b : ℝ) :
    Matrix.det ((1 : Matrix ι ι ℝ) + b • ones ι) = 1 + b * Fintype.card ι := by
  have hrep : b • ones ι =
      Matrix.replicateCol Unit (fun (_ : ι) => b) *
        Matrix.replicateRow Unit (fun (_ : ι) => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, ones]
  rw [hrep, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, mul_comm]

/-- A nonzero constant row sum allows one to strip off the constant direction
without assuming that the ambient matrix or its determinant is invertible. -/
theorem det_add_smul_ones_of_row_sum (A : Matrix ι ι ℝ) (b c : ℝ)
    (hc : c ≠ 0) (hrow : ∀ i, ∑ j, A i j = c) :
    Matrix.det (A + b • ones ι) =
      (1 + b * Fintype.card ι / c) * Matrix.det A := by
  have hfac : A + b • ones ι = A * (1 + (b / c) • ones ι) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, mul_ones_of_row_sum A c hrow,
      smul_smul, div_mul_cancel₀ _ hc]
  rw [hfac, Matrix.det_mul, det_one_add_smul_ones]
  ring

end
end UniformBlockMatrix
