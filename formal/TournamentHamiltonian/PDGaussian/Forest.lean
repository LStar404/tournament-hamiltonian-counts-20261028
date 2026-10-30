module

public import TournamentHamiltonian.PDGaussian.PhaseMGF

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PDGaussian
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem normalization_ratio {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    normalization A / normalization B = Real.sqrt (B.det / A.det) := by
  rw [normalization, normalization, Real.sqrt_div hB.det_pos.le]
  have hn : (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι ≠ 0 := by positivity
  have ha : Real.sqrt A.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA.det_pos)
  have hb : Real.sqrt B.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB.det_pos)
  field_simp

theorem phase_integral_ratio {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (b : ι → ℝ) :
    (∫ x : ι → ℝ, phaseKernel A b x) / (∫ x : ι → ℝ, realKernel B 0 x : ℝ) =
      (Real.sqrt (B.det / A.det) * Real.exp (-(b ⬝ᵥ A⁻¹ *ᵥ b)/2) : ℝ) := by
  rw [phaseKernel_integral hA, zero_integral hB, ← Complex.ofReal_div]
  congr 1
  rw [mul_div_right_comm, normalization_ratio hA hB]

/-- Actual root-gauge Lebesgue characteristic integral, relative to the empty graph. -/
theorem forest_integral_ratio {n : ℕ} (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    (∫ x : Fin n → ℝ, phaseKernel (rootMatrix F) (rootImbalance F) x) /
      (∫ x : Fin n → ℝ, realKernel (rootMatrix (emptyEdgeSet (n+1))) 0 x : ℝ) =
      (gaussianFactor F : ℂ) := by
  rw [phase_integral_ratio (rootMatrix_posDef F hm)
    (rootMatrix_posDef (emptyEdgeSet (n+1)) hm)]
  have h := rootFactor_eq_gaussianFactor F hm
  unfold rootFactor at h
  have hdec : Classical.decEq (Fin n) = instDecidableEqFin n := Subsingleton.elim _ _
  rw [hdec]
  exact congrArg Complex.ofReal h

theorem forest_integrable {n : ℕ} (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    Integrable (phaseKernel (rootMatrix F) (rootImbalance F)) :=
  phaseKernel_integrable (rootMatrix_posDef F hm) _

/-- No phase or MGF formula is assumed in this actual complete-root kernel integral. -/
theorem complete_partition (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 < a) :
    (∫ x : Fin n → ℝ, realKernel (a • completeRoot n) 0 x) =
      (Real.sqrt (2 * Real.pi))^n / Real.sqrt (a^n * (n+1 : ℝ)^(n-1)) := by
  rw [zero_integral (scaled_completeRoot_posDef n a ha), normalization]
  have h := scaled_completeRoot_det n hn a
  have hdec : Classical.decEq (Fin n) = instDecidableEqFin n := Subsingleton.elim _ _
  rw [hdec]
  simpa only [Fintype.card_fin] using congrArg
    (fun d => (Real.sqrt (2 * Real.pi))^n / Real.sqrt d) h

/-- The normalized real coordinate MGF is exp(t²/(a p)); variance parameter 2/(a p). -/
theorem complete_coordinate_MGF (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n) (t : ℝ) :
    (∫ x : Fin n → ℝ, Real.exp (-(x ⬝ᵥ (a • completeRoot n) *ᵥ x)/2 + t*x i)) /
      (∫ x : Fin n → ℝ, realKernel (a • completeRoot n) 0 x) =
      Real.exp (t^2 / (a * (n+1 : ℝ))) := by
  rw [coordinate_MGF (scaled_completeRoot_posDef n a ha)]
  have h := scaled_completeRoot_inverse_entry n a (ne_of_gt ha) i i
  have hdec : Classical.decEq (Fin n) = instDecidableEqFin n := Subsingleton.elim _ _
  rw [hdec]
  rw [h]
  simp only [ite_true]
  congr 1
  ring

theorem complete_coordinate_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n) (t : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-(x ⬝ᵥ (a • completeRoot n) *ᵥ x)/2 + t*x i)) := by
  have h := realKernel_integrable (scaled_completeRoot_posDef n a ha) (Pi.single i t)
  change Integrable (fun x => realKernel (a • completeRoot n) (Pi.single i t) x) at h
  simpa only [realKernel, single_dotProduct] using h
end PDGaussian
