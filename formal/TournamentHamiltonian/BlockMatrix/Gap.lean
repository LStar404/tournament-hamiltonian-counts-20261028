module

public import TournamentHamiltonian.BlockMatrix.Core
public import TournamentHamiltonian.BlockMatrix.TensorNorm

/-! A fixed spectral gap derived from the actual base sign matrix, not assumed. -/
set_option autoImplicit false
@[expose] public section
namespace UniformBlockMatrix
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

/-- A rational relaxation of the certified skew norm bound, chosen for `N ≥ 20`. -/
theorem signMatrix_opNorm_le_rational {d : ℕ} (T : Tournament d) (hd : 0 < d) :
    ‖signMatrix T‖ ≤ (71 / 100 : ℝ) * d := by
  have hsq := signMatrix_opNorm_sq_le T hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnorm := norm_nonneg (signMatrix T)
  nlinarith [sq_nonneg (d : ℝ)]

theorem signLift_opNorm_le {d m : ℕ} (T : Tournament d) :
    ‖signLift (m := m) T‖ ≤ (m : ℝ) * ‖signMatrix T‖ :=
  blockLift_opNorm_le (signMatrix T)

/-- The centered norm bound is obtained by the tensor and orthogonal-projection bounds. -/
theorem centered_opNorm_bound {d m : ℕ} (T : Tournament d) (hd : 0 < d)
    (hN : 1 < d * m) :
    ‖centered (m := m) T‖ ≤
      ((71 / 100 : ℝ) * (d * m : ℕ) + 1) / ((d * m : ℕ) - 1 : ℝ) := by
  have hNR : (1 : ℝ) < (d * m : ℕ) := by exact_mod_cast hN
  have hp : 0 < ((d * m : ℕ) : ℝ) - 1 := by linarith
  have hcard : 0 < Fintype.card (Vertex d m) := by rw [card_vertex]; omega
  have hlift : ‖signLift (m := m) T‖ ≤ (71 / 100 : ℝ) * (d * m : ℕ) := by
    calc
      _ ≤ (m : ℝ) * ‖signMatrix T‖ := signLift_opNorm_le T
      _ ≤ (m : ℝ) * ((71 / 100 : ℝ) * d) :=
        mul_le_mul_of_nonneg_left (signMatrix_opNorm_le_rational T hd) (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  rw [centered_eq_projection T hN, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hp)]
  calc
    _ ≤ (1 / ((d * m : ℕ) - 1 : ℝ)) *
        (‖signLift (m := m) T‖ + ‖centeringProjection (Vertex d m)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (1 / ((d * m : ℕ) - 1 : ℝ)) * ((71 / 100 : ℝ) * (d * m : ℕ) + 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hlift (centeringProjection_opNorm_le_one hcard)) (by positivity)
    _ = _ := by ring

/-- Uniform strict contraction. No regularity or desired gap is used as a hypothesis. -/
theorem centered_opNorm_le_four_fifths {d m : ℕ} (T : Tournament d)
    (hN : 20 ≤ d * m) : ‖centered (m := m) T‖ ≤ (4 / 5 : ℝ) := by
  have hNR : (20 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  have hd : 0 < d := by nlinarith
  calc
    _ ≤ _ := centered_opNorm_bound T hd (by omega)
    _ ≤ (4 / 5 : ℝ) := by
      apply (div_le_iff₀ (by linarith : 0 < ((d * m : ℕ) : ℝ) - 1)).mpr
      linarith

/-- The fixed class used by the dense-principal-minor estimates, on any finite index type. -/
structure FixedDenseClass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ D i j
  row_sum : ∀ i, (∑ j, D i j) = 1
  col_sum : ∀ j, (∑ i, D i j) = 1
  entry_le : ∀ i j, D i j ≤ 3 / (Fintype.card ι : ℝ)
  gap : ‖D - (1 / (Fintype.card ι : ℝ)) • ones ι‖ ≤ (4 / 5 : ℝ)

/-- Actual regular-base uniform-block matrices belong to the fixed class at `N ≥ 20`. -/
theorem density_mem_fixedDenseClass {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) : FixedDenseClass (density (m := m) T) where
  nonneg := density_nonneg T (by omega)
  row_sum := density_row_sum T hT (by omega)
  col_sum := density_col_sum T hT (by omega)
  entry_le := by simpa only [card_vertex] using density_entry_le (m := m) T (by omega)
  gap := by simpa only [card_vertex, centered] using centered_opNorm_le_four_fifths (m := m) T hN

/-- The determinant appearing beneath the positive square root is genuinely positive. -/
theorem centered_gram_det_pos {d m : ℕ} (T : Tournament d) (hN : 20 ≤ d * m) :
    0 < Matrix.det (1 - (centered (m := m) T).transpose * centered T) :=
  (gram_complement_posDef _ (4 / 5) (by norm_num) (by norm_num)
    (centered_opNorm_le_four_fifths T hN)).det_pos

theorem centered_gram_sqrt_pos {d m : ℕ} (T : Tournament d) (hN : 20 ≤ d * m) :
    0 < Real.sqrt (Matrix.det (1 - (centered (m := m) T).transpose * centered T)) :=
  Real.sqrt_pos.mpr (centered_gram_det_pos T hN)

end
end UniformBlockMatrix
