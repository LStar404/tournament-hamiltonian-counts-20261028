module

public import TournamentHamiltonian.BlockMatrix.TensorNorm
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator

namespace UniformBlockMatrix
noncomputable section

/-- Rectangular replication of one coordinate across an entire block. -/
def blockReplicate (d m : ℕ) : Matrix (Fin d × Fin m) (Fin d) ℝ :=
  fun u i => if u.1 = i then 1 else 0

/-- A rectangular base action followed by replication in the column index. -/
def blockRow {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d × Fin m) ℝ := fun i v => S i v.1

theorem blockReplicate_mul_blockRow {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    blockReplicate d m * blockRow S = blockLift S := by
  ext u v
  simp [Matrix.mul_apply, blockReplicate, blockRow, blockLift]

theorem blockRow_mul_blockReplicate {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    blockRow (m := m) S * blockReplicate d m = (m : ℝ) • S := by
  ext i j
  simp [Matrix.mul_apply, blockReplicate, blockRow, Fintype.sum_prod_type]

/-- Sylvester's determinant identity reduces a lifted block determinant to dimension `d`. -/
theorem det_one_add_blockLift {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.det (1 + blockLift (m := m) S) = Matrix.det (1 + (m : ℝ) • S) := by
  rw [← blockReplicate_mul_blockRow]
  rw [Matrix.det_one_add_mul_comm, blockRow_mul_blockReplicate]

@[simp] theorem blockLift_smul {d m : ℕ} (a : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    blockLift (m := m) (a • S) = a • blockLift S := rfl

@[simp] theorem blockLift_transpose {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    (blockLift (m := m) S).transpose = blockLift S.transpose := rfl

/-- Multiplication of two block lifts counts the `m` intermediate vertices per block. -/
theorem blockLift_mul {d m : ℕ} (S T : Matrix (Fin d) (Fin d) ℝ) :
    blockLift (m := m) S * blockLift T = (m : ℝ) • blockLift (S * T) := by
  ext u v
  simp [Matrix.mul_apply, blockLift, Fintype.sum_prod_type, ← Finset.mul_sum]

/-- Exact block determinant factorization; the exponent is natural and nonnegative
because every block is nonempty. The only scalar restriction is `a ≠ 0`. -/
theorem det_smul_one_add_blockLift {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hm : 1 ≤ m) (a : ℝ) (ha : a ≠ 0) :
    Matrix.det (a • (1 : Matrix (Fin d × Fin m) (Fin d × Fin m) ℝ) + blockLift S) =
      a ^ (d * m - d) * Matrix.det (a • (1 : Matrix (Fin d) (Fin d) ℝ) + (m : ℝ) • S) := by
  have hlarge : a • (1 : Matrix (Fin d × Fin m) (Fin d × Fin m) ℝ) + blockLift S =
      a • (1 + blockLift (a⁻¹ • S)) := by
    rw [smul_add, blockLift_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hsmall : a • (1 : Matrix (Fin d) (Fin d) ℝ) + (m : ℝ) • S =
      a • (1 + (m : ℝ) • (a⁻¹ • S)) := by
    rw [smul_add, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, mul_comm (m : ℝ), ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [hlarge, hsmall, Matrix.det_smul, Matrix.det_smul, det_one_add_blockLift]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← mul_assoc, ← pow_add]
  have hdim : d ≤ d * m := by nlinarith
  rw [Nat.sub_add_cancel hdim]

end
end UniformBlockMatrix
