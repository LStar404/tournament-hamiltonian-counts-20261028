module

public import TournamentHamiltonian.ForestGaussian.Laplacian
public import TournamentHamiltonian.ForestGaussian.MatrixBridge
public import TournamentHamiltonian.ForestGaussian.OperatorNorm

@[expose] public section

set_option autoImplicit false

namespace ForestGaussian
open scoped BigOperators
open Matrix
noncomputable section

variable {m : ℕ} (F : EdgeSet m)

/-- Actual finite directed-edge Gaussian determinant--phase factor.
This is not defined using the estimate or a spectral surrogate. -/
def gaussianFactor : ℝ := factor (laplacian F) (imbalance F) m

lemma laplacian_l2_operator_norm_le :
    ‖Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (laplacian F)‖ ≤ 4 :=
  posSemidef_toEuclideanCLM_norm_le_four (laplacian F)
    (laplacian_posSemidef F) (laplacian_quadratic_le F)

lemma gaussianComplement_posDef (hm : 8 ≤ m) :
    (complement (laplacian F) (m : ℝ)).PosDef := by
  apply complement_posDef (laplacian_posSemidef F).isHermitian (laplacian_quadratic_le F)
  have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

/-- The finer uniform-in-F finite estimate, proved from actual arc data. -/
theorem gaussianFactor_pos_and_log_error (hm : 8 ≤ m) :
    0 < gaussianFactor F ∧
      |Real.log (gaussianFactor F) - ((edgeCount F : ℝ) - sourceCount F) / m| ≤
        8 * ((edgeCount F : ℝ) + sourceCount F) / (m : ℝ) ^ 2 := by
  exact matrix_factor_log_error (laplacian_posSemidef F) (laplacian_quadratic_le F)
    (imbalance F) m (edgeCount F) (sourceCount F) (by exact_mod_cast hm)
    (laplacian_trace F) (sum_imbalance_sq F)

/-- Absolute C=8 for every actual directed edge set with the stated local degree
constraints, including directed cycles. No acyclicity or a=o(m) restriction. -/
theorem gaussianFactor_uniform_log_error (hm : 8 ≤ m) :
    0 < gaussianFactor F ∧
      |Real.log (gaussianFactor F) - ((edgeCount F : ℝ) - sourceCount F) / m| ≤
        8 / (m : ℝ) := by
  have h := gaussianFactor_pos_and_log_error F hm
  refine ⟨h.1, h.2.trans ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbudget : (edgeCount F : ℝ) + sourceCount F ≤ m := by
    exact_mod_cast edgeCount_add_sourceCount_le F
  calc
    _ ≤ 8 * (m : ℝ) / (m : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith
    _ = _ := by field_simp

end
end ForestGaussian
