module

public import TournamentHamiltonian.RegularContainment.Relative

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exact cancellation of the tiny forced-edge factor precedes every error estimate. -/
lemma probability_ratio_identity {k : ℕ} (F : EdgeSet (2*k+1)) (hm : 8 ≤ 2*k+1) :
    RegularOrientation.regularProbability (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F) /
      (((2:ℝ)^(edgeCount F))⁻¹*Real.exp (((edgeCount F:ℝ)-sourceCount F)/(2*k+1))) =
      normalizedRoot F/normalizedRoot (emptyEdgeSet (2*k+1)) *
        (gaussianFactor F/Real.exp (((edgeCount F:ℝ)-sourceCount F)/(2*k+1))) := by
  rw [RegularFourier.forest_regularProbability_integral, empty_rootIntegral]
  change ((((2:ℝ)^edgeCount F)⁻¹)*(torusIntegral F).re/(torusIntegral (emptyEdgeSet (2*k+1))).re)/_ = _
  rw [cancel_small_probability_factor (inv_ne_zero (pow_ne_zero _ (by norm_num : (2:ℝ)≠0)))]
  have hg : gaussianFactor F ≠ 0 := (gaussianFactor_uniform_log_error F hm).1.ne'
  have hz : Z (2*k+1) 1 ≠ 0 := (partition_pos (2*k) 1 (by norm_num)).ne'
  have hy : (torusIntegral (emptyEdgeSet (2*k+1))).re ≠ 0 := by
    have h := RegularFourier.empty_rootIntegral_pos k (RegularFourier.forestOrientation F)
    rw [empty_rootIntegral] at h
    exact h.ne'
  unfold normalizedRoot
  rw [gaussianFactor_empty]
  have hc := quarticConstant_pos.ne'
  have ht := (Real.exp_pos (((edgeCount F:ℝ)-sourceCount F)/(2*k+1))).ne'
  field_simp

def probabilityBudget (m : ℕ) : ℝ :=
  4*relativeBudget m+3*(Real.exp (8/(m:ℝ))-1)

lemma probabilityBudget_nonneg (m : ℕ) : 0 ≤ probabilityBudget m := by
  have he : 1 ≤ Real.exp (8/(m:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  unfold probabilityBudget
  nlinarith [relativeBudget_nonneg m]

lemma probabilityBudget_tendsto : Tendsto probabilityBudget atTop (𝓝 0) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 8
  have h8 : Tendsto (fun m : ℕ => 8/(m:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, div_eq_mul_inv] using hi
  have he := ((Real.continuous_exp.tendsto 0).comp h8).sub_const 1
  have hh := (relativeBudget_tendsto.const_mul 4).add (he.const_mul 3)
  unfold probabilityBudget
  simpa only [Real.exp_zero, sub_self, mul_zero, add_zero, Pi.add_apply, Function.comp_def] using hh

/-- Finite uniform bound for the actual regular-tournament conditional probability.
Oddness is explicit; the actual EdgeSet supplies local directed-arc validity. -/
theorem finite_regularProbability_bound {k : ℕ} (F : EdgeSet (2*k+1))
    (hm : 64 ≤ 2*k+1) (hb : UniformTorusTail.beta (2*k+1)<1)
    (hc : LocalLogCos.cutoff (2*k+1)≤Real.pi/8) (hk : relativeBudget (2*k+1)≤1/2) :
    |RegularOrientation.regularProbability (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F) /
      (((2:ℝ)^(edgeCount F))⁻¹*Real.exp (((edgeCount F:ℝ)-sourceCount F)/(2*k+1))) - 1| ≤
        probabilityBudget (2*k+1) := by
  rw [probability_ratio_identity F (by omega)]
  exact combined_quotient_budget (relativeBudget_nonneg _) hk
    (normalizedRoot_bound F hm hb hc) (normalizedRoot_bound (emptyEdgeSet _) hm hb hc)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      gaussianFactor_relative_error F (by omega))

/-- Uniformity is literal: N is chosen before the odd order and before F.
No assumed tail, completion, acyclicity, nonempty sample, or Gaussian surrogate probability. -/
theorem uniform_regularProbability :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k : ℕ, N ≤ 2*k+1 →
      ∀ F : EdgeSet (2*k+1),
        |RegularOrientation.regularProbability (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F) /
          (((2:ℝ)^(edgeCount F))⁻¹*Real.exp (((edgeCount F:ℝ)-sourceCount F)/(2*k+1))) - 1| ≤ η := by
  intro η hη
  have he := probabilityBudget_tendsto.eventually_lt_const hη
  have hb := UniformTorusTail.tendsto_beta_zero.eventually_lt_const (by norm_num : (0:ℝ)<1)
  have hk := relativeBudget_tendsto.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2))
  have hall : ∀ᶠ m : ℕ in atTop, 64≤m ∧ UniformTorusTail.beta m<1 ∧
      LocalLogCos.cutoff m≤Real.pi/8 ∧ relativeBudget m≤1/2 ∧ probabilityBudget m<η := by
    filter_upwards [eventually_ge_atTop 64, hb, LocalLogCos.cutoff_eventually_quarter, hk, he]
      with m hm hb' hc' hk' he'
    exact ⟨hm,hb',hc',hk',he'⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  refine ⟨N,fun k hk F => ?_⟩
  obtain ⟨hm,hb,hc,hk,he⟩ := hN (2*k+1) hk
  exact (finite_regularProbability_bound F hm hb hc hk).trans he.le

end RegularContainment
