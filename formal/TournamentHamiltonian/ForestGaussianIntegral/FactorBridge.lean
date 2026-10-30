module

public import TournamentHamiltonian.ForestGaussianIntegral.Actual
public import TournamentHamiltonian.ForestGaussian.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace ForestGaussianIntegral
open Matrix ForestGaussian
open scoped BigOperators
noncomputable section
variable {n : ℕ} (F : EdgeSet (n+1))

theorem root_quadratic_identity (x : Fin n → ℝ) :
    x ⬝ᵥ (rootMatrix F *ᵥ x) = rootLift x ⬝ᵥ (gaugeMatrix F *ᵥ rootLift x) := by
  rw [rootMatrix_eq_reduced, reduced_quadratic]
  have h : fullMatrix F - ones = gaugeMatrix F := by
    ext i j
    simp [fullMatrix, gaugeMatrix]
    ring
  rw [h]

theorem root_phase_identity (x : Fin n → ℝ) :
    rootImbalance F ⬝ᵥ x = imbalance F ⬝ᵥ rootLift x := by
  rw [dotProduct_comm (imbalance F) _, rootLift_dot]
  exact dotProduct_comm _ _

theorem rootMatrix_empty_det (hm : 8 ≤ n+1) :
    (rootMatrix (emptyEdgeSet (n+1))).det = (n+1 : ℝ)^(n-1) := by
  rw [rootMatrix_det _ hm]
  have hc : complement (laplacian (emptyEdgeSet (n+1))) (n+1 : ℝ) =
      (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := by
    ext i j
    simp [complement, emptyEdgeSet_laplacian, Matrix.one_apply]
  rw [hc, Matrix.det_one, mul_one]

theorem rootMatrix_det_ratio (hm : 8 ≤ n+1) :
    (rootMatrix (emptyEdgeSet (n+1))).det / (rootMatrix F).det =
      ((complement (laplacian F) (n+1 : ℝ)).det)⁻¹ := by
  rw [rootMatrix_empty_det hm, rootMatrix_det F hm]
  have hpow : (n+1 : ℝ)^(n-1) ≠ 0 := by positivity
  field_simp

/-- The algebraic normalization-and-phase expression suggested by a Gaussian integral formula.
It is deliberately NOT defined as an integral, and the theorem below is only an algebra bridge. -/
def rootFactor : ℝ :=
  Real.sqrt ((rootMatrix (emptyEdgeSet (n+1))).det / (rootMatrix F).det) *
    Real.exp (-(rootImbalance F ⬝ᵥ ((rootMatrix F)⁻¹ *ᵥ rootImbalance F)) / 2)

/-- Exact finite identification with the already verified full-space factor; no integral is assumed. -/
theorem rootFactor_eq_gaussianFactor (hm : 8 ≤ n+1) : rootFactor F = gaussianFactor F := by
  rw [rootFactor, rootMatrix_det_ratio F hm, Real.sqrt_inv, rootMatrix_inverse_phase F hm]
  unfold gaussianFactor factor
  have hdec : Classical.decEq (Fin (n+1)) = instDecidableEqFin (n+1) := Subsingleton.elim _ _
  rw [hdec]
  push_cast
  congr 1
  congr 1
  field_simp

end
end ForestGaussianIntegral
