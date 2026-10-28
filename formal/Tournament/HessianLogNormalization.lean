module

public import Tournament.HessianBranch
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The original logarithm is the normalized logarithm plus its constant

The manuscript uses a positive real base value `z = 2/d`. Positive real scaling
never changes a complex argument. Consequently the principal/local logarithm of
the genuine implicit branch is exactly `log z + log(h/z)` near the basepoint,
not merely another function with the same exponential. This file also records
that the actual real Hessians therefore coincide.
-/

public section

open Filter
open scoped Topology

namespace Tournament.HessianLogNormalization

/-- Positive real normalization gives equality of logarithms, not only equality
of their exponentials. -/
theorem log_eq_log_positive_add_normalized {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : w ≠ 0) :
    Complex.log w = Complex.log (r : ℂ) + Complex.log (w / (r : ℂ)) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := Complex.log_ofReal_mul hr (div_ne_zero hw hr0)
  rw [mul_div_cancel₀ _ hr0, Complex.ofReal_log hr.le] at h
  exact h

/-- The exact logarithm equality holds on a neighbourhood of every nonzero
basepoint of a continuous branch. -/
theorem eventually_log_normalization
    {X : Type*} [TopologicalSpace X] {h : X → ℂ} {x : X}
    {r : ℝ} (hr : 0 < r) (hh : ContinuousAt h x) (hn : h x ≠ 0) :
    (fun y => Complex.log (h y)) =ᶠ[𝓝 x]
      fun y => Complex.log (r : ℂ) + Complex.log (h y / (r : ℂ)) :=
  (hh.eventually_ne hn).mono fun _ hy => log_eq_log_positive_add_normalized hr hy

/-- The Hessian in the original real angle variables is unchanged by passing to
the normalized logarithm plus `log z`. -/
theorem real_hessian_log_normalization
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {h : X → ℂ} {x : X} {r : ℝ}
    (hr : 0 < r) (hh : ContinuousAt h x) (hn : h x ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun y => Complex.log (h y))) x =
      fderiv ℝ (fderiv ℝ
        (fun y => Complex.log (r : ℂ) + Complex.log (h y / (r : ℂ)))) x :=
  (eventually_log_normalization hr hh hn).fderiv.fderiv_eq

/-- Specialization to the actual determinant branch in exponential coordinates. -/
theorem branch_log_eq_normalized_eventually
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (j : ι) {r : ℝ} (hr : 0 < r)
    (hn : HessianBranch.K₁ M j (fun _ => (r : ℂ)) ≠ 0)
    (hK : HessianBranch.K M (fun _ => (r : ℂ)) = 0) :
    (fun t => Complex.log (HessianBranch.branch M j
      (HessianBranch.expCoordinates (r : ℂ) t))) =ᶠ[𝓝 (0 : ι → ℂ)]
      fun t => Complex.log (r : ℂ) + HessianBranch.logBranch M j (r : ℂ) t := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hb := HessianBranch.branch_at_base M j (fun _ => (r : ℂ)) hn hK
  have hc : ContinuousAt (fun t => HessianBranch.branch M j
      (HessianBranch.expCoordinates (r : ℂ) t)) 0 :=
    ((HessianBranch.analyticAt_branch M j _ (by simpa using hn)).comp
      (HessianBranch.analyticAt_expCoordinates (r : ℂ) 0)).continuousAt
  have hz : HessianBranch.branch M j
      (HessianBranch.expCoordinates (r : ℂ) (0 : ι → ℂ)) ≠ 0 := by
    simpa [hb] using hr0
  exact eventually_log_normalization hr hc hz

end Tournament.HessianLogNormalization
