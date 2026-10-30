module

public import TournamentHamiltonian.RegularContainment.Approximation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def relativeBudget (m : ℕ) : ℝ := Real.exp (3/2)*errorEnvelope m

def normalizedRoot (F : EdgeSet (n+1)) : ℝ :=
  (torusIntegral F).re/(quarticConstant*Z (n+1) 1*gaussianFactor F)

lemma relativeBudget_nonneg (m : ℕ) : 0 ≤ relativeBudget m :=
  mul_nonneg (Real.exp_pos _).le (errorEnvelope_nonneg m)

lemma relativeBudget_tendsto : Tendsto relativeBudget atTop (𝓝 0) := by
  unfold relativeBudget
  simpa only [mul_zero] using errorEnvelope_tendsto.const_mul (Real.exp (3/2))

lemma relative_scale_lower (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    1 ≤ Real.exp (3/2)*quarticConstant*gaussianFactor F := by
  have h := mul_le_mul_of_nonneg_left (gaussianFactor_bounds F hm).1
    (show 0 ≤ Real.exp (3/2)*quarticConstant from mul_nonneg (Real.exp_pos _).le quarticConstant_pos.le)
  have he : Real.exp (3/2)*quarticConstant*Real.exp (-1)=1 := by
    unfold quarticConstant
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rwa [he] at h

/-- Modulus-one phase and the uniform Γ lower bound turn absolute into relative error. -/
theorem normalizedRoot_bound (F : EdgeSet (n+1)) (hm : 64 ≤ n+1)
    (hb : UniformTorusTail.beta (n+1)<1)
    (hc : LocalLogCos.cutoff (n+1)≤Real.pi/8) :
    |normalizedRoot F-1| ≤ relativeBudget (n+1) := by
  have hg := (gaussianFactor_uniform_log_error F (by omega)).1
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  have hp : 0 < quarticConstant*Z (n+1) 1*gaussianFactor F := mul_pos (mul_pos quarticConstant_pos hz) hg
  unfold normalizedRoot
  rw [div_sub_one hp.ne', abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hs := mul_le_mul_of_nonneg_left (relative_scale_lower F (by omega))
    (mul_nonneg (errorEnvelope_nonneg (n+1)) hz.le)
  have ha := torus_real_approx F hm hb hc
  unfold relativeBudget
  nlinarith

lemma empty_normalizedRoot (n : ℕ) :
    normalizedRoot (emptyEdgeSet (n+1)) =
      (torusIntegral (emptyEdgeSet (n+1))).re/(quarticConstant*Z (n+1) 1) := by
  rw [normalizedRoot, gaussianFactor_empty, mul_one]

/-- Quantitative denominator lower bound, derived analytically rather than assumed. -/
theorem denominator_lower (hm : 64 ≤ n+1) (hb : UniformTorusTail.beta (n+1)<1)
    (hc : LocalLogCos.cutoff (n+1)≤Real.pi/8) (hk : relativeBudget (n+1)≤1/2) :
    quarticConstant/2*Z (n+1) 1 ≤ (torusIntegral (emptyEdgeSet (n+1))).re := by
  have h := abs_le.mp (normalizedRoot_bound (emptyEdgeSet (n+1)) hm hb hc)
  rw [empty_normalizedRoot] at h
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  have hp : 0 < quarticConstant*Z (n+1) 1 := mul_pos quarticConstant_pos hz
  have hl : 1/2 ≤ (torusIntegral (emptyEdgeSet (n+1))).re/(quarticConstant*Z (n+1) 1) := by linarith [h.1]
  have hh := (le_div_iff₀ hp).mp hl
  nlinarith

lemma empty_rootIntegral (ω : RegularOrientation.Orientation (n+1)) :
    RegularFourier.rootIntegral ∅ ω = torusIntegral (emptyEdgeSet (n+1)) := by
  have he : RegularFourier.forestEdges (emptyEdgeSet (n+1)) = ∅ := by
    simp [RegularFourier.forestEdges, emptyEdgeSet_graph]
  rw [torusIntegral, he]
  unfold RegularFourier.rootIntegral
  simp_rw [RegularFourier.empty_signedKernel]

end RegularContainment
