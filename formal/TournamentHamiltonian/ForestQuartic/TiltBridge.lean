module

public import TournamentHamiltonian.ForestQuartic.Weight

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory Matrix GaussianQuartic ForestGaussian PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def K {m : ℕ} (F : EdgeSet m) : Matrix (Fin m) (Fin m) ℝ := complement (laplacian F) m
def kernelDensity {m : ℕ} (F : EdgeSet m) : (Fin m → ℝ) → ℝ := realKernel (K F) 0

theorem K_posDef {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) : (K F).PosDef :=
  gaussianComplement_posDef F hm

theorem K_quadratic {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) :
    z ⬝ᵥ K F *ᵥ z = (∑ i, (z i)^2) - (m : ℝ)⁻¹*(z ⬝ᵥ laplacian F *ᵥ z) := by
  let _ : DecidableEq (Fin m) := Classical.decEq _
  rw [K, complement, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul]
  simp only [dotProduct, smul_eq_mul, pow_two]

theorem density_weight {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) :
    standardDensity m z * weight F z = (Real.sqrt (2*Real.pi))⁻¹^m * kernelDensity F z := by
  rw [standardDensity_formula, weight, mul_assoc, ← Real.exp_add]
  unfold kernelDensity realKernel
  simp only [zero_dotProduct, add_zero]
  rw [K_quadratic]
  congr 2
  unfold exponent
  ring

theorem weighted_integral_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (F : EdgeSet m) (f : (Fin m → ℝ) → E) :
    (∫ z, weight F z • f z ∂gaussian (Fin m)) =
      ((Real.sqrt (2*Real.pi))⁻¹^m) • ∫ z, kernelDensity F z • f z := by
  rw [integral_gaussian_density]
  simp_rw [smul_smul, density_weight, ← smul_smul]
  rw [integral_smul]

theorem weight_normalizer {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    (∫ z, weight F z ∂gaussian (Fin m)) =
      (Real.sqrt (2*Real.pi))⁻¹^m * normalization (K F) := by
  have h := weighted_integral_volume F (fun _ => (1 : ℝ))
  simpa only [smul_eq_mul, mul_one, kernelDensity, zero_integral (K_posDef F hm)] using h

theorem weight_integrable_eight {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    Integrable (weight F) (gaussian (Fin m)) := by
  rw [integrable_gaussian_density_iff]
  simp only [smul_eq_mul, density_weight]
  exact (realKernel_integrable (K_posDef F hm) 0).const_mul _

theorem tilted_probability_eight {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    IsProbabilityMeasure (tiltedMeasure F) := isProbabilityMeasure_tilted (weight_integrable_eight F hm)

/-- Actual density bridge: normalized standard-Gaussian tilt equals normalized Lebesgue K-kernel integration. -/
theorem tilted_integral_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) (f : (Fin m → ℝ) → E) :
    (∫ z, f z ∂tiltedMeasure F) = (normalization (K F))⁻¹ • ∫ z, kernelDensity F z • f z := by
  rw [tiltedMeasure, integral_tilted]
  change (∫ z, (weight F z / ∫ z, weight F z ∂gaussian (Fin m)) • f z ∂gaussian (Fin m)) = _
  have he (z : Fin m → ℝ) :
      (weight F z / ∫ z, weight F z ∂gaussian (Fin m)) • f z =
      (∫ z, weight F z ∂gaussian (Fin m))⁻¹ • (weight F z • f z) := by
    rw [smul_smul, div_eq_inv_mul]
  simp_rw [he]
  rw [integral_smul, weighted_integral_volume, weight_normalizer F hm, smul_smul]
  congr 1
  have hc : (Real.sqrt (2*Real.pi))⁻¹^m ≠ 0 := by positivity
  field_simp

theorem tilted_integrable_volume_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) (f : (Fin m → ℝ) → E) :
    Integrable f (tiltedMeasure F) ↔ Integrable (fun z => kernelDensity F z • f z) := by
  rw [tiltedMeasure, integrable_tilted_iff (weight_integrable_eight F hm)]
  change Integrable (fun z => weight F z • f z) (gaussian (Fin m)) ↔ _
  rw [integrable_gaussian_density_iff]
  simp_rw [smul_smul, density_weight, ← smul_smul]
  exact integrable_fun_smul_iff (by positivity : (Real.sqrt (2*Real.pi))⁻¹^m ≠ 0) _

theorem tilted_characteristic {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) (b : Fin m → ℝ) :
    (∫ z, Complex.exp (Complex.I*(b ⬝ᵥ z : ℝ)) ∂tiltedMeasure F) =
      (Real.exp (-(b ⬝ᵥ (K F)⁻¹ *ᵥ b)/2) : ℂ) := by
  let _ : DecidableEq (Fin m) := Classical.decEq _
  rw [tilted_integral_volume F hm]
  have he (z : Fin m → ℝ) :
      kernelDensity F z • Complex.exp (Complex.I*(b ⬝ᵥ z : ℝ)) = phaseKernel (K F) b z := by
    simp only [kernelDensity, realKernel, zero_dotProduct, add_zero, phaseKernel,
      Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, ← Complex.exp_add]
  simp_rw [he]
  rw [phaseKernel_integral (K_posDef F hm)]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (normalization_pos (K_posDef F hm)))), one_mul]
  have hdec : Classical.decEq (Fin m) = instDecidableEqFin m := Subsingleton.elim _ _
  rw [hdec]

theorem tilted_MGF {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) (b : Fin m → ℝ) :
    (∫ z, Real.exp (b ⬝ᵥ z) ∂tiltedMeasure F) = Real.exp ((b ⬝ᵥ (K F)⁻¹ *ᵥ b)/2) := by
  let _ : DecidableEq (Fin m) := Classical.decEq _
  rw [tilted_integral_volume F hm]
  have he (z : Fin m → ℝ) : kernelDensity F z • Real.exp (b ⬝ᵥ z) = realKernel (K F) b z := by
    simp only [kernelDensity, realKernel, zero_dotProduct, add_zero, smul_eq_mul, ← Real.exp_add]
  simp_rw [he]
  rw [realKernel_integral (K_posDef F hm)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (normalization_pos (K_posDef F hm))), one_mul]
  have hdec : Classical.decEq (Fin m) = instDecidableEqFin m := Subsingleton.elim _ _
  rw [hdec]
end ForestQuartic
