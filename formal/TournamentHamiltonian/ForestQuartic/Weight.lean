module

public import TournamentHamiltonian.ForestQuartic.Density

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory Matrix GaussianQuartic ForestGaussian TournamentHamiltonian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def exponent {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : ℝ :=
  (z ⬝ᵥ laplacian F *ᵥ z)/(2*m)
def weight {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : ℝ := Real.exp (exponent F z)
def tiltedMeasure {m : ℕ} (F : EdgeSet m) : Measure (Fin m → ℝ) :=
  (gaussian (Fin m)).tilted (exponent F)
def isotropic (m : ℕ) (z : Fin m → ℝ) : ℝ := Real.exp ((8/(m : ℝ))*(∑ i, (z i)^2)/2)

theorem weight_measurable {m : ℕ} (F : EdgeSet m) : Measurable (weight F) := by
  unfold weight exponent Matrix.mulVec dotProduct
  fun_prop

theorem weight_ge_one {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : 1 ≤ weight F z := by
  apply Real.one_le_exp_iff.mpr
  unfold exponent
  apply div_nonneg _ (by positivity)
  simpa only [star_trivial] using (laplacian_posSemidef F).dotProduct_mulVec_nonneg z

theorem isotropic_integrable (m : ℕ) (hm : 16 ≤ m) : Integrable (isotropic m) (gaussian (Fin m)) := by
  apply standardGaussian_quadratic_product_integrable
  have hmr : (16 : ℝ) ≤ m := by exact_mod_cast hm
  apply (div_lt_one (by positivity : (0 : ℝ) < m)).mpr
  linarith

theorem isotropic_integral (m : ℕ) (hm : 16 ≤ m) :
    (∫ z, isotropic m z ∂gaussian (Fin m)) = (Real.sqrt (1-8/(m : ℝ)))⁻¹^m := by
  have hmr : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 8/(m : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have he (z : Fin m → ℝ) : isotropic m z = ∏ i, Real.exp ((8/(m : ℝ))*(z i)^2/2) := by
    rw [isotropic, Finset.mul_sum, Finset.sum_div, Real.exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (s : ℝ) => Real.exp ((8/(m : ℝ))*s^2/2))]
  simp_rw [gaussian_quadratic_integral _ ha]
  simp

theorem isotropic_integral_le (m : ℕ) (hm : 16 ≤ m) :
    (∫ z, isotropic m z ∂gaussian (Fin m)) ≤ Real.exp 8 := by
  have hmr : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm8 : 0 < (m : ℝ)-8 := by linarith
  let a : ℝ := 1-8/(m : ℝ)
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hm0).mpr (by linarith))
  have hl : -Real.log a ≤ 1/a-1 := by
    simpa only [Real.log_inv, one_div] using Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
  have hb : (m : ℝ)/2*(1/a-1) ≤ 8 := by
    have he : a = ((m : ℝ)-8)/m := by dsimp [a]; field_simp
    rw [he]
    have he' : (m : ℝ)/2*(1/(((m : ℝ)-8)/m)-1) = 4*m/((m : ℝ)-8) := by
      field_simp [ne_of_gt hm0, ne_of_gt hm8]
      ring
    rw [he']
    apply (div_le_iff₀ hm8).mpr
    linarith
  have hexp : -(m : ℝ)*Real.log a/2 ≤ 8 := by
    have h := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (m : ℝ)/2)
    nlinarith
  rw [isotropic_integral m hm, inv_pow]
  have hs : (Real.sqrt a)^m = Real.exp ((m : ℝ)*Real.log a/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha, ← Real.exp_nat_mul]
    congr 1
    ring
  change ((Real.sqrt a)^m)⁻¹ ≤ _
  rw [hs, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem weight_sq_le {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) (z : Fin m → ℝ) :
    (weight F z)^2 ≤ isotropic m z := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [weight, ← Real.exp_nat_mul, isotropic]
  apply Real.exp_le_exp.mpr
  have h := laplacian_quadratic_le F z
  unfold exponent
  field_simp
  norm_num at *
  nlinarith

theorem weight_sq_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (fun z => (weight F z)^2) (gaussian (Fin m)) := by
  apply (isotropic_integrable m hm).mono' ((weight_measurable F).pow_const 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (weight F z))]
  exact weight_sq_le F hm z

theorem weight_memLp {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    MemLp (weight F) 2 (gaussian (Fin m)) :=
  (memLp_two_iff_integrable_sq (weight_measurable F).aestronglyMeasurable).mpr (weight_sq_integrable F hm)

theorem weight_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (weight F) (gaussian (Fin m)) := (weight_memLp F hm).integrable (by norm_num)

theorem weight_integral_ge_one {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    1 ≤ ∫ z, weight F z ∂gaussian (Fin m) := by
  calc
    1 = ∫ _z : Fin m → ℝ, (1 : ℝ) ∂gaussian (Fin m) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (weight_integrable F hm) (weight_ge_one F)

theorem weight_sq_integral_le {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, (weight F z)^2 ∂gaussian (Fin m)) ≤ Real.exp 8 :=
  (integral_mono (weight_sq_integrable F hm) (isotropic_integrable m hm) (weight_sq_le F hm)).trans
    (isotropic_integral_le m hm)

theorem tilted_probability {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    IsProbabilityMeasure (tiltedMeasure F) := isProbabilityMeasure_tilted (weight_integrable F hm)

theorem cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x*g x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (∫ x, (g x)^2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hf' hg'
  simpa only [Real.norm_eq_abs, ← abs_mul, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using h

theorem weighted_abs_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) {g : (Fin m → ℝ) → ℝ}
    (hg : MemLp g 2 (gaussian (Fin m))) :
    (∫ z, weight F z * |g z| ∂gaussian (Fin m)) ≤
      Real.exp 4 * Real.sqrt (∫ z, (g z)^2 ∂gaussian (Fin m)) := by
  have h := cauchy_schwarz (gaussian (Fin m)) (weight_memLp F hm) hg
  have habs (z : Fin m → ℝ) : |weight F z| = weight F z := abs_of_pos (Real.exp_pos _)
  simp_rw [abs_mul, habs] at h
  change (∫ z, weight F z*|g z| ∂gaussian (Fin m)) ≤ _ at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  calc
    Real.sqrt (∫ z, (weight F z)^2 ∂gaussian (Fin m)) ≤ Real.sqrt (Real.exp 8) :=
      Real.sqrt_le_sqrt (weight_sq_integral_le F hm)
    _ = Real.exp 4 := by
      have he : Real.exp 8 = (Real.exp 4)^2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
end ForestQuartic
