module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LogTaylorAtOne
open Set Filter
open scoped Topology

def logCosh (x : ℝ) : ℝ := Real.log (Real.cosh x)
def negLogCos (x : ℝ) : ℝ := -Real.log (Real.cos x)

def hyperbolicJet : ℕ → ℝ → ℝ
  | 0, x => logCosh x
  | 1, x => Real.tanh x
  | 2, x => 1-(Real.tanh x)^2
  | 3, x => -2*Real.tanh x*(1-(Real.tanh x)^2)
  | _, _ => 0

def circularJet : ℕ → ℝ → ℝ
  | 0, x => negLogCos x
  | 1, x => Real.tan x
  | 2, x => 1+(Real.tan x)^2
  | 3, x => 2*Real.tan x*(1+(Real.tan x)^2)
  | _, _ => 0

theorem tanh_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1-(Real.tanh x)^2) x := by
  have hc := (Real.cosh_pos x).ne'
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc using 1
  · ext y
    simp [Real.tanh_eq_sinh_div_cosh]
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

theorem tan_derivative {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1+(Real.tan x)^2) x := by
  have he : 1/(Real.cos x)^2 = 1+(Real.tan x)^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [← he]
  exact Real.hasDerivAt_tan hx

theorem hyperbolicJet_hasDerivAt (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    HasDerivAt (hyperbolicJet k) (hyperbolicJet (k+1) x) x := by
  have h := tanh_derivative x
  interval_cases k
  · change HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x
    convert (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne' using 1
    simp [Real.tanh_eq_sinh_div_cosh]
  · exact h
  · change HasDerivAt (fun y => 1-(Real.tanh y)^2) (-2*Real.tanh x*(1-(Real.tanh x)^2)) x
    convert (h.pow 2).const_sub 1 using 1; ring

theorem circularJet_hasDerivAt (k : ℕ) (hk : k ≤ 2) {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (circularJet k) (circularJet (k+1) x) x := by
  have h := tan_derivative hx
  interval_cases k
  · change HasDerivAt (fun y => -Real.log (Real.cos y)) (Real.tan x) x
    convert ((Real.hasDerivAt_cos x).log hx).neg using 1
    simp [Real.tan_eq_sin_div_cos, neg_div]
  · exact h
  · change HasDerivAt (fun y => 1+(Real.tan y)^2) (2*Real.tan x*(1+(Real.tan x)^2)) x
    convert (h.pow 2).const_add 1 using 1; ring

theorem iteratedDeriv_logCosh (k : ℕ) (hk : k ≤ 3) (x : ℝ) :
    iteratedDeriv k logCosh x = hyperbolicJet k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k logCosh = hyperbolicJet k := funext (ih (by omega))
    rw [he]
    exact (hyperbolicJet_hasDerivAt k (by omega) x).deriv

theorem iteratedDeriv_negLogCos (k : ℕ) (hk : k ≤ 3) {x : ℝ} (hx : Real.cos x ≠ 0) :
    iteratedDeriv k negLogCos x = circularJet k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k negLogCos =ᶠ[𝓝 x] circularJet k := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact ih (by omega) hy
    rw [he.deriv_eq]
    exact (circularJet_hasDerivAt k (by omega) hx).deriv
end LogTaylorAtOne
