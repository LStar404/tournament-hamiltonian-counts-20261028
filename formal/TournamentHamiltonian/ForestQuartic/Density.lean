module

public import TournamentHamiltonian.GaussianQuartic.Limit
public import TournamentHamiltonian.PDGaussian.PhaseMGF
public import Mathlib.MeasureTheory.Measure.Tilted

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory Matrix GaussianQuartic
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Product of the actual one-dimensional standard Gaussian Lebesgue densities. -/
def standardDensity (m : ℕ) (z : Fin m → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (z i)

theorem standardDensity_nonneg (m : ℕ) (z : Fin m → ℝ) : 0 ≤ standardDensity m z :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (z i))

theorem standardDensity_measurable (m : ℕ) : Measurable (standardDensity m) := by
  unfold standardDensity
  fun_prop

theorem standardDensity_integrable (m : ℕ) : Integrable (standardDensity m) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

/-- Genuine product Gaussian = genuine Lebesgue measure with its actual product density. -/
theorem gaussian_eq_withDensity (m : ℕ) :
    gaussian (Fin m) = volume.withDensity (fun z => ENNReal.ofReal (standardDensity m z)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (standardDensity_integrable m).restrict
      (ae_of_all _ (standardDensity_nonneg m))]
  change ENNReal.ofReal (∫ z, standardDensity m z ∂
    (Measure.pi (fun _ : Fin m => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  unfold standardDensity
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0) (s i)).symm

theorem integral_gaussian_density {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (f : (Fin m → ℝ) → E) :
    (∫ z, f z ∂gaussian (Fin m)) = ∫ z, standardDensity m z • f z := by
  rw [gaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (standardDensity_measurable m).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (standardDensity_nonneg m _)]

theorem integrable_gaussian_density_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (f : (Fin m → ℝ) → E) :
    Integrable f (gaussian (Fin m)) ↔ Integrable (fun z => standardDensity m z • f z) := by
  rw [gaussian_eq_withDensity, integrable_withDensity_iff_integrable_smul'
    (standardDensity_measurable m).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (standardDensity_nonneg m _)]

theorem standardDensity_formula (m : ℕ) (z : Fin m → ℝ) :
    standardDensity m z = (Real.sqrt (2*Real.pi))⁻¹^m * Real.exp (-(∑ i, (z i)^2)/2) := by
  unfold standardDensity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  congr 1
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
end ForestQuartic
