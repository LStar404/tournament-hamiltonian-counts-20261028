module

public import TournamentHamiltonian.LogTaylorAtOne.Derivatives
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LogTaylorAtOne
open Set

theorem third_logCosh_abs_le (x : ℝ) : |iteratedDeriv 3 logCosh x| ≤ 2 := by
  rw [iteratedDeriv_logCosh 3 (by omega) x]
  have ht := (Real.abs_tanh_lt_one x).le
  have hsq := (Real.tanh_sq_lt_one x).le
  have hs : 0 ≤ 1-(Real.tanh x)^2 := sub_nonneg.mpr hsq
  have hu : 1-(Real.tanh x)^2 ≤ 1 := by nlinarith [sq_nonneg (Real.tanh x)]
  have hp := mul_le_mul ht hu hs (by norm_num : (0:ℝ)≤1)
  simpa only [hyperbolicJet, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ)≤2), abs_of_nonneg hs, mul_assoc, one_mul, mul_one] using
    mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)

theorem cos_pos_on_unit {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [hx.1, hx.2, Real.pi_gt_three]

theorem tan_bounds_on_unit {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    0 ≤ Real.tan x ∧ Real.tan x ≤ Real.tan 1 := by
  have h0 : (0:ℝ) ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by constructor <;> linarith [Real.pi_pos]
  have h1 : (1:ℝ) ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by constructor <;> linarith [Real.pi_gt_three]
  have hxx : x ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by constructor <;> linarith [hx.1, hx.2, Real.pi_gt_three]
  constructor
  · simpa only [Real.tan_zero] using Real.strictMonoOn_tan.monotoneOn h0 hxx hx.1
  · exact Real.strictMonoOn_tan.monotoneOn hxx h1 hx.2

theorem sec_sq_identity {x : ℝ} (hx : Real.cos x ≠ 0) :
    1+(Real.tan x)^2 = 1/(Real.cos x)^2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- The actual third derivative on the segment used by §10.4. -/
theorem third_negLogCos_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    iteratedDeriv 3 negLogCos x = 2*Real.tan x/(Real.cos x)^2 := by
  rw [iteratedDeriv_negLogCos 3 (by omega) (cos_pos_on_unit hx).ne']
  simp only [circularJet, sec_sq_identity (cos_pos_on_unit hx).ne']
  ring

theorem third_negLogCos_abs_le {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    |iteratedDeriv 3 negLogCos x| ≤ 2*Real.tan 1/(Real.cos 1)^2 := by
  rw [iteratedDeriv_negLogCos 3 (by omega) (cos_pos_on_unit hx).ne']
  have ht := tan_bounds_on_unit hx
  have h1 := (tan_bounds_on_unit (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp)).1
  have hsq : (Real.tan x)^2 ≤ (Real.tan 1)^2 := sq_le_sq₀ ht.1 h1 |>.mpr ht.2
  have hsq' : 1+(Real.tan x)^2 ≤ 1+(Real.tan 1)^2 := by linarith
  have htx := ht.1
  have hp := mul_le_mul ht.2 hsq' (by positivity : 0≤1+(Real.tan x)^2) h1
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)
  change |2*Real.tan x*(1+(Real.tan x)^2)| ≤ _
  rw [abs_of_nonneg (by positivity)]
  calc
    _ ≤ 2*Real.tan 1*(1+(Real.tan 1)^2) := by nlinarith
    _ = _ := by rw [sec_sq_identity (cos_pos_on_unit (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)).ne']; ring
end LogTaylorAtOne
