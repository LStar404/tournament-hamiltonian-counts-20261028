module

public import TournamentHamiltonian.ForestGaussianIntegral.Determinant

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace ForestGaussianIntegral
open Matrix ForestGaussian
open scoped BigOperators
noncomputable section
variable {n : ℕ} (F : EdgeSet (n+1))

/-- The full positive-definite quadratic matrix m I - L_F, with m=n+1. -/
def fullMatrix : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (n+1 : ℝ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - laplacian F

/-- The actual singular root-gauge quadratic matrix m I - J - L_F. -/
def gaugeMatrix : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (n+1 : ℝ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - ones - laplacian F

/-- The principal minor obtained by deleting root 0. -/
def rootMatrix : Matrix (Fin n) (Fin n) ℝ := (gaugeMatrix F).submatrix Fin.succ Fin.succ

def rootImbalance : Fin n → ℝ := rootTail (imbalance F)

theorem fullMatrix_eq_scaled_complement : fullMatrix F =
    (n+1 : ℝ) • complement (laplacian F) (n+1 : ℝ) := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  simp [fullMatrix, complement, smul_sub, smul_smul, hn]
  ext i j
  simp [Matrix.one_apply]

theorem rootMatrix_eq_reduced : rootMatrix F = reduced (fullMatrix F) := by
  ext i j
  simp [rootMatrix, reduced, gaugeMatrix, fullMatrix]
  ring

theorem fullMatrix_row_sum :
    fullMatrix F *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ) := by
  simp [fullMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, laplacian_mulVec_one]

theorem fullMatrix_posDef (hm : 8 ≤ n+1) : (fullMatrix F).PosDef := by
  rw [fullMatrix_eq_scaled_complement]
  have h := gaussianComplement_posDef F hm
  push_cast at h
  exact h.smul (by positivity)

theorem rootMatrix_posDef (hm : 8 ≤ n+1) : (rootMatrix F).PosDef := by
  rw [rootMatrix_eq_reduced]
  exact reduced_posDef (fullMatrix_posDef F hm) (fullMatrix_row_sum F)

/-- Exact grounded determinant, m=n+1: det A_F = m^(m-2) det(I-L_F/m). -/
theorem rootMatrix_det (hm : 8 ≤ n+1) :
    (rootMatrix F).det = (n+1 : ℝ)^(n-1) * (complement (laplacian F) (n+1 : ℝ)).det := by
  rw [rootMatrix_eq_reduced, reduced_det (fullMatrix_posDef F hm).isHermitian (fullMatrix_row_sum F),
    fullMatrix_eq_scaled_complement, Matrix.det_smul]
  simp only [Fintype.card_fin]
  have hn : n+1 = (n-1)+2 := by omega
  have hp : (n+1 : ℝ)^(n+1) = (n+1 : ℝ)^(n-1) * (n+1 : ℝ)^2 := by rw [hn, pow_add]
  rw [hp]
  have hn0 : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem fullMatrix_inverse_apply (hm : 8 ≤ n+1) (b : Fin (n+1) → ℝ) :
    (fullMatrix F)⁻¹ *ᵥ b =
      (n+1 : ℝ)⁻¹ • ((complement (laplacian F) (n+1 : ℝ))⁻¹ *ᵥ b) := by
  have hH := fullMatrix_posDef F hm
  have hK : (complement (laplacian F) (n+1 : ℝ)).PosDef := by
    simpa only [Nat.cast_add, Nat.cast_one] using gaussianComplement_posDef F hm
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  apply hH.mulVec_injective
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    Matrix.one_mulVec, fullMatrix_eq_scaled_complement, Matrix.smul_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne'), Matrix.one_mulVec]
  simp [smul_smul, hn]

/-- Exact endpoint phase: b'ᵀ A_F⁻¹ b' = (1/m) bᵀ K_F⁻¹ b. -/
theorem rootMatrix_inverse_phase (hm : 8 ≤ n+1) :
    rootImbalance F ⬝ᵥ ((rootMatrix F)⁻¹ *ᵥ rootImbalance F) =
      (n+1 : ℝ)⁻¹ * (imbalance F ⬝ᵥ
        ((complement (laplacian F) (n+1 : ℝ))⁻¹ *ᵥ imbalance F)) := by
  rw [rootImbalance, rootMatrix_eq_reduced,
    reduced_inverse_quadratic (fullMatrix_posDef F hm) (fullMatrix_row_sum F) _ (sum_imbalance F),
    fullMatrix_inverse_apply F hm, dotProduct_smul]
  rfl

end
end ForestGaussianIntegral
