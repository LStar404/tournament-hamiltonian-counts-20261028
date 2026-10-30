module

public import TournamentHamiltonian.ForestQuartic.Concentration
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory Matrix GaussianQuartic ForestGaussian PDGaussian Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Actual identification with mathlib's Gaussian law; no covariance or concentration premise. -/
theorem tilted_euclidean_law {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    (tiltedMeasure F).map (WithLp.toLp 2) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (K F)⁻¹ := by
  let dec : DecidableEq (Fin m) := Classical.decEq _
  let _ : IsProbabilityMeasure (tiltedMeasure F) := tilted_probability_eight F hm
  have hdec : dec = instDecidableEqFin m := Subsingleton.elim _ _
  rw [← hdec]
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_multivariateGaussian (K_posDef F hm).inv.posSemidef]
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have he (z : Fin m → ℝ) :
      Complex.exp ((inner ℝ (WithLp.toLp 2 z) t : ℝ) * Complex.I) =
      Complex.exp (Complex.I * (t.ofLp ⬝ᵥ z : ℝ)) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm, mul_comm]
  simp_rw [he]
  rw [tilted_characteristic F hm]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, neg_div]
  rw [hdec]

theorem gaussian_expDeviation_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (fun y : EuclideanSpace ℝ (Fin m) => expDeviation F y.ofLp)
      (multivariateGaussian 0 (K F)⁻¹) := by
  have hp : MeasurePreserving (WithLp.toLp 2) (tiltedMeasure F)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (K F)⁻¹) :=
    ⟨by fun_prop, tilted_euclidean_law F (by omega)⟩
  exact (hp.integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding).mp
    (expDeviation_integrable F hm)

/-- Concentration under mathlib's actual multivariate Gaussian with covariance K^-1. -/
theorem gaussian_expDeviation_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ y : EuclideanSpace ℝ (Fin m), expDeviation F y.ofLp
      ∂multivariateGaussian 0 (K F)⁻¹) ≤ errorRate m := by
  rw [← tilted_euclidean_law F (by omega), integral_map (by fun_prop)]
  · exact expDeviation_bound F hm
  · unfold expDeviation forestQuartic edge4
    fun_prop

theorem gaussian_exp_L1_tendsto (F : ∀ m : ℕ, EdgeSet m) :
    Tendsto (fun m => ∫ y : EuclideanSpace ℝ (Fin m), expDeviation (F m) y.ofLp
      ∂multivariateGaussian 0 (K (F m))⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun m => integral_nonneg (fun _ => abs_nonneg _)))
    _ errorRate_tendsto
  filter_upwards [eventually_ge_atTop 16] with m hm
  exact gaussian_expDeviation_bound (F m) hm

end ForestQuartic
