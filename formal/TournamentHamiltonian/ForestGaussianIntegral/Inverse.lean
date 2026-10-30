module

public import TournamentHamiltonian.ForestGaussianIntegral.Coordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace ForestGaussianIntegral
open Matrix
open scoped BigOperators
noncomputable section
variable {n : ℕ}

theorem centered_quadratic {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hH : H.IsHermitian)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) :
    centered x ⬝ᵥ (H *ᵥ centered x) = x ⬝ᵥ ((H - ones) *ᵥ x) := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  simp [centered, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.sub_mulVec,
    hrow, ones_mulVec, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    dot_one, one_dot, sum_mulVec hH hrow]
  field_simp
  ring

theorem reduced_posDef {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hH : H.PosDef)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ)) :
    (reduced H).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(hH.isHermitian.sub ones_isHermitian).submatrix Fin.succ, ?_⟩
  intro x hx
  simpa only [star_trivial, reduced_quadratic, ← centered_quadratic hH.isHermitian hrow] using
    hH.dotProduct_mulVec_pos (centered_lift_ne_zero x hx)

theorem root_matrix_zero_mode {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ)) :
    (H - ones) *ᵥ (1 : Fin (n+1) → ℝ) = 0 := by
  simp [Matrix.sub_mulVec, hrow, ones_mulVec]

theorem reduced_inverse_quadratic {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hH : H.PosDef)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ))
    (b : Fin (n+1) → ℝ) (hb : ∑ i, b i = 0) :
    rootTail b ⬝ᵥ ((reduced H)⁻¹ *ᵥ rootTail b) = b ⬝ᵥ (H⁻¹ *ᵥ b) := by
  let y := H⁻¹ *ᵥ b
  have hy : H *ᵥ y = b := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hsumy : ∑ i, y i = 0 := by
    have h := sum_mulVec hH.isHermitian hrow y
    rw [hy, hb] at h
    have hn : 0 < (n+1 : ℝ) := by positivity
    nlinarith
  have hMy : (H - ones) *ᵥ y = b := by
    rw [Matrix.sub_mulVec, ones_mulVec, hsumy, zero_smul, sub_zero, hy]
  have hMg : (H - ones) *ᵥ gauge y = b := by
    rw [gauge, Matrix.mulVec_sub, Matrix.mulVec_smul, root_matrix_zero_mode hrow,
      smul_zero, sub_zero, hMy]
  have hAg : reduced H *ᵥ rootTail (gauge y) = rootTail b := by
    rw [reduced_mulVec, ← gauge_eq_lift_tail, hMg]
  have hx : (reduced H)⁻¹ *ᵥ rootTail b = rootTail (gauge y) := by
    rw [← hAg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (reduced_posDef hH hrow).det_pos.ne'),
      Matrix.one_mulVec]
  rw [hx]
  calc
    rootTail b ⬝ᵥ rootTail (gauge y) = b ⬝ᵥ gauge y := by
      simp [dotProduct, Fin.sum_univ_succ, rootTail, gauge_zero]
    _ = b ⬝ᵥ y := by
      rw [gauge, dotProduct_sub, dotProduct_smul, dot_one, hb]
      simp
    _ = _ := rfl

end
end ForestGaussianIntegral
