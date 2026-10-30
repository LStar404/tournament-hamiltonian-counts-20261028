module

public import TournamentHamiltonian.BlockMatrix.ScalarRatio

set_option autoImplicit false
@[expose] public section

namespace UniformBlockMatrix
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

/-- The real lifted sign matrix remains skew-symmetric. -/
theorem signLift_transpose {d m : ℕ} (T : Tournament d) :
    (signLift (m := m) T).transpose = -signLift T := by
  ext u v
  exact signMatrix_skew T v.1 u.1

/-- Regularity annihilates the constant direction on the right. -/
theorem signLift_mul_ones {d m : ℕ} (T : Tournament d) (hT : IsRegular T) :
    signLift (m := m) T * ones (Vertex d m) = 0 := by
  ext u v
  simpa [Matrix.mul_apply, ones, hT u.1] using signLift_row_sum (m := m) T u

/-- Regularity annihilates the constant direction on the left. -/
theorem ones_mul_signLift {d m : ℕ} (T : Tournament d) (hT : IsRegular T) :
    ones (Vertex d m) * signLift T = 0 := by
  ext u v
  simpa [Matrix.mul_apply, ones, hT v.1] using signLift_col_sum (m := m) T v

/-- The centering projection acts as identity on the lifted skew action. -/
theorem signLift_mul_centering {d m : ℕ} (T : Tournament d) (hT : IsRegular T) :
    signLift (m := m) T * centeringProjection (Vertex d m) = signLift T := by
  rw [centeringProjection_eq]
  change signLift T * (1 - _ • ones (Vertex d m)) = _
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, signLift_mul_ones T hT,
    smul_zero, sub_zero]

/-- The same projection identity holds on the left. -/
theorem centering_mul_signLift {d m : ℕ} (T : Tournament d) (hT : IsRegular T) :
    centeringProjection (Vertex d m) * signLift T = signLift T := by
  rw [centeringProjection_eq]
  change (1 - _ • ones (Vertex d m)) * signLift T = _
  rw [Matrix.sub_mul, Matrix.one_mul, smul_mul_assoc, ones_mul_signLift T hT,
    smul_zero, sub_zero]

/-- Before tensor reduction, the centered Gram is a sum of the projection and skew square. -/
theorem centered_transpose_mul {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 1 < d * m) :
    (centered (m := m) T).transpose * centered T =
      blockStep d m ^ 2 •
        (centeringProjection (Vertex d m) - signLift T * signLift T) := by
  have hp : 0 < Fintype.card (Vertex d m) := by rw [card_vertex]; omega
  have hsym : (centeringProjection (Vertex d m)).transpose =
      centeringProjection (Vertex d m) := rankOneComplement_transpose _
  have hid : centeringProjection (Vertex d m) * centeringProjection (Vertex d m) =
      centeringProjection (Vertex d m) :=
    rankOneComplement_idempotent _ (flatUnitVector_sum_sq _ hp)
  rw [centered_eq_projection T hN]
  change (blockStep d m • (signLift T - centeringProjection (Vertex d m))).transpose *
    (blockStep d m • (signLift T - centeringProjection (Vertex d m))) = _
  rw [Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul, smul_smul,
    ← pow_two, Matrix.transpose_sub, signLift_transpose, hsym,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.neg_mul,
    Matrix.neg_mul, signLift_mul_centering T hT, centering_mul_signLift T hT, hid]
  congr 1
  abel

/-- Exact full-size Gram matrix, including its constant-direction correction. -/
theorem centered_gram_eq_block {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 1 < d * m) :
    1 - (centered (m := m) T).transpose * centered T =
      (1 - blockStep d m ^ 2) • (1 : Matrix (Vertex d m) (Vertex d m) ℝ) +
      blockLift ((blockStep d m ^ 2 * (m : ℝ)) • (signMatrix T * signMatrix T) +
        (blockStep d m ^ 2 / (d * m : ℕ)) • ones (Fin d)) := by
  rw [centered_transpose_mul T hT hN, centeringProjection_eq]
  change 1 - blockStep d m ^ 2 •
    ((1 - ((Fintype.card (Vertex d m) : ℝ)⁻¹) • ones (Vertex d m)) -
      blockLift (signMatrix T) * blockLift (signMatrix T)) = _
  rw [blockLift_mul, card_vertex]
  ext u v
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    blockLift_apply, ones]
  ring

/-- The full base shift retains the scalar constant-direction eigenvalue `-h`. -/
theorem baseShift_gram_eq {d m : ℕ} (T : Tournament d) :
    1 - (baseShift (m := m) T).transpose * baseShift (m := m) T =
      (1 - blockStep d m ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (blockStep d m ^ 2 * (m : ℝ) ^ 2) • (signMatrix T * signMatrix T) := by
  rw [baseShift, Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul,
    smul_smul, ← pow_two, Matrix.transpose_sub, Matrix.transpose_smul,
    signMatrix_transpose, Matrix.transpose_one,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    smul_mul_assoc, Matrix.mul_smul, smul_smul, smul_neg,
    Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Squaring the base sign matrix still annihilates the constant vector. -/
theorem signMatrix_sq_row_sum {d : ℕ} (T : Tournament d) (hT : IsRegular T)
    (i : Fin d) : (∑ j, (signMatrix T * signMatrix T) i j) = 0 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ k, signMatrix T i k * score T k) = 0
  apply Finset.sum_eq_zero
  intro k _
  rw [hT k, mul_zero]

/-- The Gram determinant's constant-direction factor is exactly `1-h²`. -/
theorem baseShift_gram_row_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (i : Fin d) :
    (∑ j, (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T) i j) =
      1 - blockStep d m ^ 2 := by
  rw [baseShift_gram_eq]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, signMatrix_sq_row_sum T hT, mul_zero, add_zero]
  simp [Matrix.one_apply]

end
end UniformBlockMatrix
