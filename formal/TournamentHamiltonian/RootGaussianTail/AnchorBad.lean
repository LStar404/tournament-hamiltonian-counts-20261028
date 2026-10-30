module

public import TournamentHamiltonian.RootGaussianTail.Anchor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory Set PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A general translated root weight, including density times a bad-set indicator. -/
def anchorWeight (n : ℕ) (f : (Fin n → ℝ) → ℝ) (y : ℝ × (Fin n → ℝ)) : ℝ :=
  f (fun i => y.2 i-y.1)

theorem anchorWeight_integrable (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) (hfm : Measurable f) (l u : ℝ) :
    Integrable (anchorWeight n f) (anchorMeasure n l u) := by
  have hm : Measurable (anchorWeight n f) := hfm.comp (by fun_prop)
  rw [anchorMeasure, integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => hf.comp_sub_right (fun _ => t))
  · have he (t : ℝ) : (∫ x : Fin n → ℝ, ‖anchorWeight n f (t,x)‖) =
        ∫ x : Fin n → ℝ, ‖f x‖ := integral_sub_right_eq_self (fun x => ‖f x‖) (fun _ => t)
    simp_rw [he]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem anchorWeight_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) (hfm : Measurable f) (l u : ℝ) :
    (∫ y, anchorWeight n f y ∂anchorMeasure n l u) = max (u-l) 0 * ∫ x, f x := by
  rw [anchorMeasure, integral_prod _ (anchorWeight_integrable n f hf hfm l u)]
  have he (t : ℝ) : (∫ x : Fin n → ℝ, anchorWeight n f (t,x)) = ∫ x, f x :=
    integral_sub_right_eq_self f (fun _ => t)
  simp_rw [he]
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]

theorem anchorWeight_box_bound (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (l u : ℝ)
    (E : Set (ℝ × (Fin n → ℝ))) :
    (∫ y in E, anchorWeight n f y ∂anchorMeasure n l u) ≤ max (u-l) 0 * ∫ x, f x := by
  have h := setIntegral_le_integral (s := E) (anchorWeight_integrable n f hf hfm l u)
    (ae_of_all _ (fun y => hf0 (fun i => y.2 i-y.1)))
  exact h.trans_eq (anchorWeight_integral n f hf hfm l u)

theorem density_measurable (n : ℕ) (a : ℝ) : Measurable (density n a) := by
  unfold density realKernel Matrix.mulVec dotProduct
  fun_prop

theorem rootSet_anchor_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S) (l u : ℝ) :
    Integrable (anchorWeight n (S.indicator (density n a))) (anchorMeasure n l u) :=
  anchorWeight_integrable n _ ((density_integrable n a ha).indicator hS)
    ((density_measurable n a).indicator hS) l u

/-- The root bad-set integral, not the full normalizer, controls a short-anchor box. -/
theorem rootSet_anchor_box_bound (n : ℕ) (a : ℝ) (ha : 0 < a) (S : Set (Fin n → ℝ))
    (hS : MeasurableSet S) (l u : ℝ) (E : Set (ℝ × (Fin n → ℝ))) :
    (∫ y in E, anchorWeight n (S.indicator (density n a)) y ∂anchorMeasure n l u) ≤
      max (u-l) 0 * ∫ x in S, density n a x := by
  have h := anchorWeight_box_bound n (S.indicator (density n a))
    ((density_integrable n a ha).indicator hS) ((density_measurable n a).indicator hS)
    (fun x => by by_cases hx : x ∈ S <;> simp [hx, density_nonneg n a x]) l u E
  simpa only [integral_indicator hS] using h

theorem maxTail_anchor_box_bound (n : ℕ) (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t)
    (l u : ℝ) (E : Set (ℝ × (Fin n → ℝ))) :
    (∫ y in E, anchorWeight n ((maxTail n t).indicator (density n a)) y ∂anchorMeasure n l u) ≤
      max (u-l) 0 * (2*n*partition n a*Real.exp (-a*(n+1 : ℝ)*t^2/4)) := by
  exact (rootSet_anchor_box_bound n a ha _ (maxTail_measurable n t) l u E).trans
    (mul_le_mul_of_nonneg_left (finite_max_tail n a ha t ht) (le_max_right _ _))
end RootGaussianTail
