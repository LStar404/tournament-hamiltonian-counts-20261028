module

public import TournamentHamiltonian.BlockMatrix.Gap
public import TournamentHamiltonian.BlockMatrix.Determinant
public import TournamentHamiltonian.BlockMatrix.ConstantDet

/-! Safe scalar and square-root foundations for the fixed-base determinant ratio.
The final ratio factorization and fixed-dimension limit are intentionally not claimed here. -/
set_option autoImplicit false
@[expose] public section
namespace UniformBlockMatrix
open TournamentHamiltonian
open scoped Matrix.Norms.L2Operator
noncomputable section

def blockStep (d m : ℕ) : ℝ := 1 / ((d * m : ℕ) - 1 : ℝ)

def scalarRatio (d m : ℕ) : ℝ :=
  (1 + blockStep d m) / Real.sqrt (1 - blockStep d m ^ 2)

/-- This is the full `d × d` matrix, including its extra constant-direction eigenvalue. -/
def baseShift {d m : ℕ} (T : Tournament d) : Matrix (Fin d) (Fin d) ℝ :=
  blockStep d m • ((m : ℝ) • signMatrix T - 1)

/-- Uncentered determinant ratio; unlike `R(D)`, this does not subtract an averaging matrix. -/
def rawRatio {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Matrix ι ι ℝ) : ℝ :=
  Matrix.det (1 - Z) / Real.sqrt (Matrix.det (1 - Z.transpose * Z))

theorem blockStep_pos {d m : ℕ} (hN : 2 ≤ d * m) : 0 < blockStep d m := by
  have hNR : (2 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  exact div_pos (by norm_num) (by linarith)

theorem blockStep_lt_one {d m : ℕ} (hN : 3 ≤ d * m) : blockStep d m < 1 := by
  have hNR : (3 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  unfold blockStep
  apply (div_lt_one (by linarith)).mpr
  linarith

theorem scalar_gram_pos {d m : ℕ} (hN : 3 ≤ d * m) : 0 < 1 - blockStep d m ^ 2 := by
  have hpos := blockStep_pos (by omega : 2 ≤ d * m)
  have hlt := blockStep_lt_one hN
  nlinarith

theorem scalar_sqrt_pos {d m : ℕ} (hN : 3 ≤ d * m) :
    0 < Real.sqrt (1 - blockStep d m ^ 2) := Real.sqrt_pos.mpr (scalar_gram_pos hN)

theorem scalarRatio_pos {d m : ℕ} (hN : 3 ≤ d * m) : 0 < scalarRatio d m := by
  exact div_pos (by linarith [blockStep_pos (by omega : 2 ≤ d * m)]) (scalar_sqrt_pos hN)

/-- The complete base shift also has a derived fixed gap, so its determinant root is safe. -/
theorem baseShift_opNorm_le_four_fifths {d m : ℕ} (T : Tournament d)
    (hN : 20 ≤ d * m) : ‖baseShift (m := m) T‖ ≤ (4 / 5 : ℝ) := by
  have hd : 0 < d := by nlinarith
  let : NeZero d := ⟨by omega⟩
  have hNR : (20 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  have hp : 0 < ((d * m : ℕ) : ℝ) - 1 := by linarith
  have hs : (m : ℝ) * ‖signMatrix T‖ ≤ (71 / 100 : ℝ) * (d * m : ℕ) := by
    calc
      _ ≤ (m : ℝ) * ((71 / 100 : ℝ) * d) :=
        mul_le_mul_of_nonneg_left (signMatrix_opNorm_le_rational T hd) (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  rw [baseShift, norm_smul, Real.norm_eq_abs,
    abs_of_pos (blockStep_pos (by omega))]
  calc
    _ ≤ blockStep d m * (‖(m : ℝ) • signMatrix T‖ + ‖(1 : Matrix (Fin d) (Fin d) ℝ)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (blockStep_pos (by omega)).le
    _ = blockStep d m * ((m : ℝ) * ‖signMatrix T‖ + 1) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_one]
    _ ≤ blockStep d m * ((71 / 100 : ℝ) * (d * m : ℕ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (blockStep_pos (by omega)).le
    _ ≤ 4 / 5 := by
      unfold blockStep
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hp).mpr
      linarith

theorem baseShift_gram_det_pos {d m : ℕ} (T : Tournament d) (hN : 20 ≤ d * m) :
    0 < Matrix.det (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T) :=
  (gram_complement_posDef _ (4 / 5) (by norm_num) (by norm_num)
    (baseShift_opNorm_le_four_fifths T hN)).det_pos

theorem baseShift_gram_sqrt_pos {d m : ℕ} (T : Tournament d) (hN : 20 ≤ d * m) :
    0 < Real.sqrt (Matrix.det (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T)) :=
  Real.sqrt_pos.mpr (baseShift_gram_det_pos T hN)

end
end UniformBlockMatrix
