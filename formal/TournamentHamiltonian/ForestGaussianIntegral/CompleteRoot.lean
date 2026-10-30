module

public import TournamentHamiltonian.ForestGaussianIntegral.FactorBridge

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace ForestGaussianIntegral
open Matrix ForestGaussian
open scoped BigOperators
noncomputable section

def rootOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

/-- Complete-graph root matrix, before an additional positive kernel scale. -/
def completeRoot (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (n+1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - rootOnes n

theorem completeRoot_eq_reduced (n : ℕ) :
    completeRoot n = reduced ((n+1 : ℝ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) := by
  ext i j
  simp [completeRoot, reduced, ones, rootOnes, Matrix.one_apply]

theorem completeRoot_posDef (n : ℕ) : (completeRoot n).PosDef := by
  rw [completeRoot_eq_reduced]
  apply reduced_posDef ((Matrix.PosDef.one).smul (by positivity : 0 < (n+1 : ℝ)))
  simp [Matrix.smul_mulVec]

theorem completeRoot_inverse (n : ℕ) :
    (completeRoot n)⁻¹ = (n+1 : ℝ)⁻¹ •
      ((1 : Matrix (Fin n) (Fin n) ℝ) + rootOnes n) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  simp [completeRoot, rootOnes, Matrix.mul_apply, Matrix.one_apply, sub_mul, mul_add,
    ite_mul, mul_ite, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hij : i = j <;> simp [hij] <;> field_simp <;> ring

theorem completeRoot_empty (n : ℕ) : rootMatrix (emptyEdgeSet (n+1)) = completeRoot n := by
  rw [rootMatrix_eq_reduced, fullMatrix]
  simp [emptyEdgeSet_laplacian, completeRoot_eq_reduced]

/-- The inverse of a positively scaled complete root matrix, valid also at dimension zero. -/
theorem scaled_completeRoot_inverse (n : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (a • completeRoot n)⁻¹ = (a * (n+1 : ℝ))⁻¹ •
      ((1 : Matrix (Fin n) (Fin n) ℝ) + rootOnes n) := by
  have hi : (a • completeRoot n)⁻¹ = a⁻¹ • (completeRoot n)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (completeRoot_posDef n).det_pos.ne')]
    simp [smul_smul, ha]
  rw [hi, completeRoot_inverse, smul_smul, mul_inv]

/-- Inverse-matrix entries. For positive a these are candidate Gaussian covariance entries;
no probability law identification is claimed here. -/
theorem scaled_completeRoot_inverse_entry (n : ℕ) (a : ℝ) (ha : a ≠ 0) (i j : Fin n) :
    (a • completeRoot n)⁻¹ i j =
      (if i = j then 2 else 1) / (a * (n+1 : ℝ)) := by
  rw [scaled_completeRoot_inverse n a ha]
  by_cases hij : i = j <;> norm_num [rootOnes, hij, div_eq_mul_inv, mul_comm]

theorem completeRoot_det (n : ℕ) (hn : 1 ≤ n) :
    (completeRoot n).det = (n+1 : ℝ)^(n-1) := by
  rw [completeRoot_eq_reduced,
    reduced_det ((Matrix.PosDef.one).smul (by positivity : 0 < (n+1 : ℝ))).isHermitian
      (by simp [Matrix.smul_mulVec]), Matrix.det_smul, Matrix.det_one]
  simp only [Fintype.card_fin, mul_one]
  have he : n+1 = (n-1)+2 := by omega
  rw [he, pow_add]
  have hm0 : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem scaled_completeRoot_det (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    (a • completeRoot n).det = a^n * (n+1 : ℝ)^(n-1) := by
  rw [Matrix.det_smul, completeRoot_det n hn, Fintype.card_fin]

theorem scaled_completeRoot_posDef (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (a • completeRoot n).PosDef := (completeRoot_posDef n).smul ha

end
end ForestGaussianIntegral
