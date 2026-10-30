module

public import TournamentHamiltonian.BlockMatrix.ScalarRatio

set_option autoImplicit false
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Exact block form of the numerator matrix for the actual centered uniform density. -/
theorem one_sub_centered_eq_block {d m : ℕ} (T : Tournament d) (hN : 1 < d * m) :
    1 - centered (m := m) T =
      (1 + blockStep d m) • (1 : Matrix (Vertex d m) (Vertex d m) ℝ) +
        blockLift ((-blockStep d m) • signMatrix T -
          (blockStep d m / (d * m : ℕ)) • ones (Fin d)) := by
  rw [centered_eq_projection T hN, centeringProjection_eq]
  ext u v
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    blockLift, signLift, ones, Matrix.of_apply, card_vertex, blockStep]
  ring

/-- The full base-shift numerator retains the constant-direction factor `1+h`. -/
theorem one_sub_baseShift_row_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (i : Fin d) : (∑ j, (1 - baseShift (m := m) T) i j) = 1 + blockStep d m := by
  classical
  simp only [baseShift, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs : (∑ j, signMatrix T i j) = 0 := hT i
  simp [hs, Matrix.one_apply]

/-- Exact numerator factorization, with the extra base constant direction divided out. -/
theorem centered_numerator_det {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) :
    Matrix.det (1 - centered (m := m) T) =
      (1 + blockStep d m) ^ (d * m - d) * Matrix.det (1 - baseShift (m := m) T) /
        (1 + blockStep d m) := by
  have hm : 1 ≤ m := by nlinarith
  have hNR : (20 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  have hN0 : ((d * m : ℕ) : ℝ) ≠ 0 := by linarith
  have hp : 0 < 1 + blockStep d m := by
    linarith [blockStep_pos (by omega : 2 ≤ d * m)]
  rw [one_sub_centered_eq_block T (by omega),
    det_smul_one_add_blockLift _ hm _ hp.ne']
  have heq : (1 + blockStep d m) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (m : ℝ) • ((-blockStep d m) • signMatrix T -
        (blockStep d m / (d * m : ℕ)) • ones (Fin d)) =
      (1 - baseShift (m := m) T) +
        (-(m : ℝ) * blockStep d m / (d * m : ℕ)) • ones (Fin d) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, baseShift]
    ring
  rw [heq, det_add_smul_ones_of_row_sum _ _ (1 + blockStep d m) hp.ne'
    (one_sub_baseShift_row_sum T hT)]
  have hc : 1 + (-(m : ℝ) * blockStep d m / (d * m : ℕ)) *
      (Fintype.card (Fin d) : ℝ) / (1 + blockStep d m) = 1 / (1 + blockStep d m) := by
    simp only [Fintype.card_fin]
    have hmul : (m : ℝ) * d = (d * m : ℕ) := by push_cast; ring
    field_simp
    nlinarith
  rw [hc]
  ring

end
end UniformBlockMatrix
