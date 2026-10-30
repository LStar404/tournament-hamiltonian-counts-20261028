module

public import TournamentHamiltonian.UniformTorusTail.Sum
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The shrinking-window scale from the proof plan. -/
def window (m : ℕ) (eps : ℝ) : ℝ := (m : ℝ)^(-(1:ℝ)/2+eps)

def farEnvelope (m : ℕ) : ℝ := 16*Real.pi^(m-1)/Z m 1*farConstant m
def outlierEnvelope (m : ℕ) : ℝ := 16*Real.exp 4*(beta m/(1-beta m))
def localEnvelope (m : ℕ) (t : ℝ) : ℝ :=
  32*Real.exp 4*(m-1 : ℕ)*Real.exp (-((m : ℝ)-4)*t^2/4)

lemma beta_rpow (m : ℕ) :
    beta m = (Real.pi*Real.sqrt (Real.exp 1/(2*Real.pi))) *
      (m : ℝ)^((3:ℝ)/2) * Real.exp (-(kappa1/2)*(m : ℝ)) := by
  have hs : Real.exp 1*(m : ℝ)/(2*Real.pi) = (Real.exp 1/(2*Real.pi))*(m : ℝ) := by ring
  have hpow : (m : ℝ)^((3:ℝ)/2) = (m : ℝ)*Real.sqrt (m : ℝ) := by
    by_cases hm : m=0
    · subst m; norm_num
    · have hm0 : (0 : ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [show (3:ℝ)/2=1+1/2 by norm_num, Real.rpow_add hm0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold beta q
  rw [hs, Real.sqrt_mul (by positivity), hpow]
  have he : -kappa1*(m : ℝ)/2 = -(kappa1/2)*(m : ℝ) := by ring
  rw [he]
  ring

/-- The beta expression is exactly the planned sqrt(eπ/2)m^(3/2) formula. -/
lemma beta_eq_plan (m : ℕ) :
    beta m = Real.sqrt (Real.exp 1*Real.pi/2)*(m : ℝ)^((3:ℝ)/2)*
      Real.exp (-kappa1*(m : ℝ)/2) := by
  rw [beta_rpow]
  have hs : Real.pi*Real.sqrt (Real.exp 1/(2*Real.pi)) = Real.sqrt (Real.exp 1*Real.pi/2) := by
    calc
      Real.pi*Real.sqrt (Real.exp 1/(2*Real.pi)) =
          Real.sqrt (Real.pi^2*(Real.exp 1/(2*Real.pi))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]
      _ = _ := by congr 1; field_simp
  rw [hs]
  congr 2
  ring

lemma tendsto_beta_zero : Tendsto beta atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((3:ℝ)/2) (kappa1/2)
    (div_pos kappa1_pos (by norm_num))).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := h.const_mul (Real.pi*Real.sqrt (Real.exp 1/(2*Real.pi)))
  simpa only [mul_zero, Function.comp_def, ← mul_assoc, ← beta_rpow] using hc

lemma tendsto_outlierEnvelope_zero : Tendsto outlierEnvelope atTop (𝓝 0) := by
  change Tendsto (fun m => 16*Real.exp 4*(beta m/(1-beta m))) atTop (𝓝 0)
  have hd := tendsto_beta_zero.div (tendsto_const_nhds.sub tendsto_beta_zero) (by norm_num : (1:ℝ)-0≠0)
  have h := hd.const_mul (16*Real.exp 4)
  simpa only [sub_zero, zero_div, mul_zero, outlierEnvelope, Pi.div_apply] using h

/-- Any polynomial times a stretched exponential tends to zero. -/
lemma tendsto_stretched_exp (d b s : ℝ) (hd : 0 < d) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x^s*Real.exp (-b*x^d)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s/d) b hb).comp (tendsto_rpow_atTop hd)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp [Function.comp_def]
  rw [← Real.rpow_mul hx.le]
  congr 2
  field_simp

lemma window_exponent_lower (m : ℕ) (hm : 8 ≤ m) (eps : ℝ) :
    (m : ℝ)^(2*eps)/8 ≤ ((m : ℝ)-4)*(window m eps)^2/4 := by
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hm8 : (8:ℝ)≤m := by exact_mod_cast hm
  have he : (m : ℝ)*(window m eps)^2 = (m : ℝ)^(2*eps) := by
    calc
      (m : ℝ)*(window m eps)^2 = (m : ℝ)^((1:ℝ))* (m : ℝ)^((-(1:ℝ)/2+eps)*2) := by
        rw [Real.rpow_mul hm0.le, Real.rpow_two, Real.rpow_one]
        rfl
      _ = _ := by rw [← Real.rpow_add hm0]; congr 1; ring
  rw [← he]
  nlinarith [sq_nonneg (window m eps)]

lemma tendsto_localEnvelope_window_zero (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun m => localEnvelope m (window m eps)) atTop (𝓝 0) := by
  have h := (tendsto_stretched_exp (2*eps) (1/8) 1 (by positivity) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper := h.const_mul (32*Real.exp 4)
  simp only [Real.rpow_one, mul_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall (fun m => by unfold localEnvelope; positivity)
  · filter_upwards [eventually_ge_atTop (8:ℕ)] with m hm
    have hm1 : 1≤m := by omega
    have hle := window_exponent_lower m hm eps
    unfold localEnvelope
    have hexp : Real.exp (-((m : ℝ)-4)*(window m eps)^2/4) ≤ Real.exp (-(1/8)*(m : ℝ)^(2*eps)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hnat : ((m-1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
    have hh := mul_le_mul hnat hexp (Real.exp_pos _).le (Nat.cast_nonneg _)
    have hhh := mul_le_mul_of_nonneg_left hh (show 0 ≤ 32*Real.exp 4 by positivity)
    simpa only [mul_assoc, Function.comp_def] using hhh

/-- The log of the far-volume/normalizer ratio, scaled by m². -/
def scaledFar (x : ℝ) : ℝ :=
  (1-x⁻¹)*Real.log Real.pi*x⁻¹ - (1-x⁻¹)*Real.log (2*Real.pi)*x⁻¹/2 +
    (1-2*x⁻¹)*(Real.log x/x)/2 - kappa0/128

lemma tendsto_scaledFar : Tendsto scaledFar atTop (𝓝 (-kappa0/128)) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hl : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  unfold scaledFar
  have h := (((((tendsto_const_nhds (x := (1:ℝ))).sub hi).mul_const (Real.log Real.pi)).mul hi).sub
    ((((tendsto_const_nhds (x := (1:ℝ))).sub hi).mul_const (Real.log (2*Real.pi))).mul hi |>.div_const 2)).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub (hi.const_mul 2)).mul hl |>.div_const 2)
  simpa only [Pi.sub_apply, sub_zero, zero_mul, mul_zero, zero_div, zero_add, zero_sub, neg_div] using h.sub_const (kappa0/128)

lemma farEnvelope_exp (m : ℕ) (hm : 2 ≤ m) :
    farEnvelope m = 16*Real.exp (scaledFar m*(m : ℝ)^2) := by
  have hm0 : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hpi : Real.pi^(m-1) = Real.exp (((m-1 : ℕ) : ℝ)*Real.log Real.pi) := by
    rw [Real.exp_nat_mul, Real.exp_log Real.pi_pos]
  rw [farEnvelope, farConstant, Z_one_exp m hm, hpi, mul_div_assoc, ← Real.exp_sub,
    mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  rw [Nat.cast_sub (by omega : 1≤m), Nat.cast_one]
  unfold scaledFar
  field_simp; ring

lemma tendsto_farEnvelope_zero : Tendsto farEnvelope atTop (𝓝 0) := by
  have hn : -kappa0/128 < 0 := by have h := kappa0_pos; linarith
  have hexponent := tendsto_scaledFar.neg_mul_atTop hn (tendsto_pow_atTop (by decide : 2≠0))
  have h := (Real.tendsto_exp_atBot.comp hexponent).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := h.const_mul 16
  simp only [mul_zero] at hc
  apply hc.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with m hm
  exact (farEnvelope_exp m hm).symm

end UniformTorusTail
