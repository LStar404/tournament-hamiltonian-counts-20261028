module

public import TournamentHamiltonian.ForestGaussianIntegral.Inverse

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
namespace ForestGaussianIntegral
open Matrix
open scoped BigOperators
noncomputable section
variable {n : ℕ}

/-- The first column is the normalized constant vector; all other columns are coordinate vectors. -/
def gaugeBasis (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if j = 0 then (n+1 : ℝ)⁻¹ else if i = j then 1 else 0

theorem gaugeBasis_det (n : ℕ) : (gaugeBasis n).det = (n+1 : ℝ)⁻¹ := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [gaugeBasis]
  · intro i j hij
    change i < j at hij
    have hj : j ≠ 0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
    simp [gaugeBasis, hj, ne_of_lt hij]

def rootEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem H_mul_gaugeBasis {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ))
    (i j : Fin (n+1)) :
    (H * gaugeBasis n) i j = if j = 0 then 1 else H i j := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hs : ∑ k, H i k = n+1 := by
    have h := congrFun hrow i
    simpa [Matrix.mulVec, dotProduct] using h
  by_cases hj : j = 0
  · subst j
    simp [Matrix.mul_apply, gaugeBasis, ← Finset.sum_mul, hs, hn]
  · simp [Matrix.mul_apply, gaugeBasis, hj, mul_ite]

theorem gaugeBasis_congruence {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hH : H.IsHermitian)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ))
    (i j : Fin (n+1)) :
    ((gaugeBasis n)ᵀ * H * gaugeBasis n) i j =
      if i = 0 ∨ j = 0 then 1 else H i j := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hs : ∑ k, H k j = n+1 := by
    have h := congrFun (col_sum hH hrow) j
    simpa [Matrix.vecMul, dotProduct] using h
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp_rw [H_mul_gaugeBasis hrow]
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j; simp [gaugeBasis, Matrix.transpose_apply, hn]
    · simp [gaugeBasis, Matrix.transpose_apply, hj, ← Finset.mul_sum, hs, hn]
  · simp [gaugeBasis, Matrix.transpose_apply, hi, ite_mul]

/-- Finite grounded determinant identity, with no integral formula as a premise. -/
theorem reduced_det {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hH : H.IsHermitian)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ)) :
    (reduced H).det = H.det / (n+1 : ℝ)^2 := by
  let C : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
    Matrix.fromBlocks 1 (fun _ _ => 1) (fun _ _ => 1) (H.submatrix Fin.succ Fin.succ)
  have heq : ((gaugeBasis n)ᵀ * H * gaugeBasis n).submatrix (rootEquiv n) (rootEquiv n) = C := by
    ext i j
    rcases i with ⟨⟩ | i <;> rcases j with ⟨⟩ | j <;>
      simp [Matrix.submatrix_apply, rootEquiv, gaugeBasis_congruence hH hrow, C,
        Matrix.fromBlocks]
  have hC : C.det = (reduced H).det := by
    dsimp [C]
    rw [Matrix.det_fromBlocks_one₁₁]
    congr 1
    ext i j
    simp [reduced, ones, Matrix.mul_apply]
  rw [← hC, ← heq, Matrix.det_submatrix_equiv_self, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, gaugeBasis_det]
  field_simp

end
end ForestGaussianIntegral
