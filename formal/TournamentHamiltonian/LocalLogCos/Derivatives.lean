module

public import TournamentHamiltonian.RootObservable.Quartic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Set Filter
open scoped Topology BigOperators

def logCos (x : ℝ) : ℝ := Real.log (Real.cos x)
def jet : ℕ → ℝ → ℝ
  | 0, x => logCos x
  | 1, x => -Real.tan x
  | 2, x => -(1+(Real.tan x)^2)
  | 3, x => -(2*Real.tan x+2*(Real.tan x)^3)
  | 4, x => -(2+8*(Real.tan x)^2+6*(Real.tan x)^4)
  | 5, x => -(16*Real.tan x+40*(Real.tan x)^3+24*(Real.tan x)^5)
  | 6, x => -(16+136*(Real.tan x)^2+240*(Real.tan x)^4+120*(Real.tan x)^6)
  | _, _ => 0

theorem tan_derivative {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1+(Real.tan x)^2) x := by
  have he : 1/(Real.cos x)^2 = 1+(Real.tan x)^2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [← he]
  exact Real.hasDerivAt_tan hx

theorem jet_hasDerivAt (k : ℕ) (hk : k ≤ 5) {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (jet k) (jet (k+1) x) x := by
  have h := tan_derivative hx
  interval_cases k
  · change HasDerivAt (fun y => Real.log (Real.cos y)) (-Real.tan x) x
    convert (Real.hasDerivAt_cos x).log hx using 1
    simp [Real.tan_eq_sin_div_cos, neg_div]
  · change HasDerivAt (fun y => -Real.tan y) (-(1+(Real.tan x)^2)) x
    exact h.neg
  · change HasDerivAt (fun y => -(1+(Real.tan y)^2)) (-(2*Real.tan x+2*(Real.tan x)^3)) x
    convert ((h.pow 2).const_add 1).neg using 1; ring
  · change HasDerivAt (fun y => -(2*Real.tan y+2*(Real.tan y)^3)) (-(2+8*(Real.tan x)^2+6*(Real.tan x)^4)) x
    convert ((h.const_mul 2).add ((h.pow 3).const_mul 2)).neg using 1; ring
  · change HasDerivAt (fun y => -(2+8*(Real.tan y)^2+6*(Real.tan y)^4)) (-(16*Real.tan x+40*(Real.tan x)^3+24*(Real.tan x)^5)) x
    convert ((((h.pow 2).const_mul 8).const_add 2).add ((h.pow 4).const_mul 6)).neg using 1; ring
  · change HasDerivAt (fun y => -(16*Real.tan y+40*(Real.tan y)^3+24*(Real.tan y)^5))
      (-(16+136*(Real.tan x)^2+240*(Real.tan x)^4+120*(Real.tan x)^6)) x
    convert (((h.const_mul 16).add ((h.pow 3).const_mul 40)).add ((h.pow 5).const_mul 24)).neg using 1; ring

theorem iteratedDeriv_logCos (k : ℕ) (hk : k ≤ 6) {x : ℝ} (hx : Real.cos x ≠ 0) :
    iteratedDeriv k logCos x = jet k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k logCos =ᶠ[𝓝 x] jet k := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hx] with y hy
      exact ih (by omega) hy
    rw [he.deriv_eq]
    exact (jet_hasDerivAt k (by omega) hx).deriv

theorem cos_pos_of_abs_le_quarter {x : ℝ} (hx : |x| ≤ Real.pi/4) : 0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_le] at hx
  constructor <;> linarith [Real.pi_pos]

theorem abs_tan_le_one {x : ℝ} (hx : |x| ≤ Real.pi/4) : |Real.tan x| ≤ 1 := by
  have hxx : x ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    rw [abs_le] at hx
    constructor <;> linarith [Real.pi_pos]
  have hp : Real.pi/4 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by constructor <;> linarith [Real.pi_pos]
  have hn : -(Real.pi/4) ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by constructor <;> linarith [Real.pi_pos]
  rw [abs_le] at hx ⊢
  constructor
  · have h := Real.strictMonoOn_tan.monotoneOn hn hxx hx.1
    simpa [Real.tan_neg, Real.tan_pi_div_four] using h
  · have h := Real.strictMonoOn_tan.monotoneOn hxx hp hx.2
    simpa [Real.tan_pi_div_four] using h

theorem sixth_derivative_bounds {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    -512 ≤ iteratedDeriv 6 logCos x ∧ iteratedDeriv 6 logCos x ≤ 0 := by
  rw [iteratedDeriv_logCos 6 (by omega) (cos_pos_of_abs_le_quarter hx).ne']
  have h2 : (Real.tan x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (abs_tan_le_one hx)
  have h4 : (Real.tan x)^4 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg (Real.tan x)) (sub_nonneg.mpr h2)]
  have h6 : (Real.tan x)^6 ≤ 1 := by
    have h := mul_le_mul h2 h4 (by positivity) (by norm_num : (0:ℝ)≤1)
    nlinarith
  simp only [jet]
  constructor <;> nlinarith [sq_nonneg (Real.tan x), sq_nonneg ((Real.tan x)^2), sq_nonneg ((Real.tan x)^3)]
end LocalLogCos
