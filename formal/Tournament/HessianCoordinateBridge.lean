module

public import Tournament.HessianDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Eliminating a coordinate in an actual analytic zero set

This adapts the differential bridge to the full-coordinate determinant branch:
a coordinate is cleared by `T` and reinserted by `e`. Unlike a finite-dimensional
chart construction, this keeps the original index set and its selected coordinate.
Analyticity supplies all derivative-existence hypotheses; only the actual two-jet
of the constraint remains to be calculated in the concrete resolvent module.
-/

public section

open Filter
open scoped Topology

namespace Tournament.HessianCoordinateBridge

open Tournament.HessianDerivatives

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

@[expose] noncomputable def parameterDeriv (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y)
    (A : X →L[ℂ] ℂ) : X →L[ℂ] Y := T + e.comp A

@[expose] noncomputable def parameterSecond (e : ℂ →L[ℂ] Y)
    (B : X →L[ℂ] X →L[ℂ] ℂ) : X →L[ℂ] X →L[ℂ] Y :=
  (ContinuousLinearMap.compL ℂ X ℂ Y e).comp B

@[simp] theorem parameterDeriv_apply (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y)
    (A : X →L[ℂ] ℂ) (v : X) : parameterDeriv T e A v = T v + e (A v) := rfl

@[simp] theorem parameterSecond_apply (e : ℂ →L[ℂ] Y)
    (B : X →L[ℂ] X →L[ℂ] ℂ) (v w : X) : parameterSecond e B v w = e (B v w) := rfl

theorem hasFDerivAt_parameter
    (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y)
    {g : X → ℂ} {A : X →L[ℂ] ℂ} {x : X} (hg : HasFDerivAt g A x) :
    HasFDerivAt (fun y => T y + e (g y)) (parameterDeriv T e A) x := by
  exact T.hasFDerivAt.add (e.hasFDerivAt.comp x hg)

theorem hasFDerivAt_parameterDeriv
    (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y)
    {g₁ : X → X →L[ℂ] ℂ} {B : X →L[ℂ] X →L[ℂ] ℂ} {x : X}
    (h : HasFDerivAt g₁ B x) :
    HasFDerivAt (fun y => parameterDeriv T e (g₁ y)) (parameterSecond e B) x := by
  have hc := (ContinuousLinearMap.compL ℂ X ℂ Y e).hasFDerivAt.comp x h
  convert! (hasFDerivAt_const T x).add hc using 1
  simp [parameterSecond]

/-- The actual complex Hessian of the eliminated coordinate. `mass` is the sum
of coordinates in the manuscript; `mass (e s) = s` fixes its normalization. -/
theorem implicit_coordinate_hessian
    {φ : Y → ℂ} {g : X → ℂ}
    (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y) (mass : Y →L[ℂ] ℂ)
    (Q : Y →L[ℂ] Y →L[ℂ] ℂ) {d : ℂ} (hd : d ≠ 0)
    (he : ∀ s, mass (e s) = s)
    (hφ : AnalyticAt ℂ φ 0) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hzero : (fun t => φ (T t + e (g t))) =ᶠ[𝓝 (0 : X)] fun _ => 0)
    (hfirst : ∀ z, fderiv ℂ φ 0 z = -mass z / d)
    (hsecond : ∀ z t, fderiv ℂ (fderiv ℂ φ) 0 z t = -Q z t / d)
    (v w : X) :
    fderiv ℂ (fderiv ℂ g) 0 v w =
      -Q (T v - e (mass (T v))) (T w - e (mass (T w))) := by
  let g₁ := fderiv ℂ g
  let g₂ := fderiv ℂ (fderiv ℂ g) 0
  have hg₁ : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt g (g₁ y) y :=
    hg.eventually_analyticAt.mono fun _ h => h.differentiableAt.hasFDerivAt
  have hg₂ : HasFDerivAt g₁ g₂ 0 := hg.fderiv.differentiableAt.hasFDerivAt
  have hφ₁ : ∀ᶠ y in 𝓝 (T 0 + e (g 0)),
      HasFDerivAt φ (fderiv ℂ φ y) y := by
    simpa [hg0] using hφ.eventually_analyticAt.mono
      (fun _ h => h.differentiableAt.hasFDerivAt)
  have hφ₂ : HasFDerivAt (fderiv ℂ φ) (fderiv ℂ (fderiv ℂ φ) 0)
      (T 0 + e (g 0)) := by
    simpa [hg0] using hφ.fderiv.differentiableAt.hasFDerivAt
  have hγ : ∀ᶠ y in 𝓝 (0 : X),
      HasFDerivAt (fun t => T t + e (g t)) (parameterDeriv T e (g₁ y)) y :=
    hg₁.mono fun _ h => hasFDerivAt_parameter T e h
  have hγ₂ := hasFDerivAt_parameterDeriv T e hg₂
  have hgrad : ∀ u, g₁ 0 u = -mass (T u) := by
    intro u
    have hf := hφ₁.self_of_nhds.comp 0 hγ.self_of_nhds
    have hz : HasFDerivAt (fun t => φ (T t + e (g t))) 0 0 :=
      (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) (0 : X)).congr_of_eventuallyEq hzero
    have hval := congrArg (fun A : X →L[ℂ] ℂ => A u) (hf.unique hz)
    have hv : -(mass (T u) + g₁ 0 u) / d = 0 := by
      simpa [hg0, hfirst, he] using hval
    apply (eq_neg_iff_add_eq_zero).2
    simpa [add_comm] using neg_eq_zero.mp ((div_eq_zero_iff.mp hv).resolve_right hd)
  have h := implicit_second_identity
    (g := fun t => T t + e (g t))
    (g₁ := fun t => parameterDeriv T e (g₁ t))
    (g₂ := parameterSecond e g₂) hφ₁ hφ₂ hγ hγ₂ hzero v w
  simp only [parameterDeriv_apply, parameterSecond_apply, hg0, map_zero, add_zero] at h
  rw [hsecond, hfirst, he, hgrad v, hgrad w, map_neg, map_neg] at h
  have hv : -(Q (T v - e (mass (T v))) (T w - e (mass (T w))) + g₂ v w) / d = 0 := by
    simpa only [sub_eq_add_neg, neg_add, add_div, add_comm] using h
  apply (eq_neg_iff_add_eq_zero).2
  simpa [g₂, add_comm] using neg_eq_zero.mp ((div_eq_zero_iff.mp hv).resolve_right hd)

/-- The final real-angle Hessian bridge for full-coordinate analytic branches. -/
theorem real_angle_coordinate_hessian
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
    {φ : Y → ℂ} {g : X → ℂ}
    (T : X →L[ℂ] Y) (e : ℂ →L[ℂ] Y) (mass : Y →L[ℂ] ℂ)
    (Q : Y →L[ℂ] Y →L[ℂ] ℂ) {d : ℂ} (hd : d ≠ 0)
    (he : ∀ s, mass (e s) = s)
    (hφ : AnalyticAt ℂ φ 0) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hzero : (fun t => φ (T t + e (g t))) =ᶠ[𝓝 (0 : X)] fun _ => 0)
    (hfirst : ∀ z, fderiv ℂ φ 0 z = -mass z / d)
    (hsecond : ∀ z t, fderiv ℂ (fderiv ℂ φ) 0 z t = -Q z t / d)
    (L : R →L[ℝ] X) (a : ℂ) (v w : R) :
    fderiv ℝ (fderiv ℝ (fun t => a + g (Complex.I • L t))) 0 v w =
      Q (T (L v) - e (mass (T (L v)))) (T (L w) - e (mass (T (L w)))) := by
  have hg₁ : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt g (fderiv ℂ g y) y :=
    hg.eventually_analyticAt.mono fun _ h => h.differentiableAt.hasFDerivAt
  rw [second_real_angle hg₁ hg.fderiv.differentiableAt.hasFDerivAt L a v w,
    implicit_coordinate_hessian T e mass Q hd he hφ hg hg0 hzero hfirst hsecond,
    neg_neg]

end Tournament.HessianCoordinateBridge
