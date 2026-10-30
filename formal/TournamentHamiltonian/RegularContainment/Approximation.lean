module

public import TournamentHamiltonian.RegularContainment.Local

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

lemma cutoff_eq_window (m : ℕ) : LocalLogCos.cutoff m = UniformTorusTail.window m (1/16) := by
  unfold LocalLogCos.cutoff UniformTorusTail.window
  congr 1
  norm_num

def errorEnvelope (m : ℕ) : ℝ :=
  |UniformTorusTail.tailEnvelope m (1/16)| +
    Real.exp 4*(LocalLogCos.cutoffError m+ForestQuartic.errorRate m) +
    quarticConstant*gaussianTailBudget m (LocalLogCos.cutoff m)

lemma errorEnvelope_nonneg (m : ℕ) : 0 ≤ errorEnvelope m := by
  unfold errorEnvelope LocalLogCos.cutoffError ForestQuartic.errorRate
  exact add_nonneg (add_nonneg (abs_nonneg _) (by positivity))
    (mul_nonneg quarticConstant_pos.le (gaussianTailBudget_nonneg _ _))

lemma errorEnvelope_tendsto : Tendsto errorEnvelope atTop (𝓝 0) := by
  have ht := (UniformTorusTail.tendsto_tailEnvelope_zero (1/16) (by norm_num)).abs
  have hl := (LocalLogCos.cutoffError_tendsto.add ForestQuartic.errorRate_tendsto).const_mul (Real.exp 4)
  have hg := gaussianTailBudget_tendsto.const_mul quarticConstant
  simp_rw [← cutoff_eq_window] at hg
  unfold errorEnvelope
  simpa only [abs_zero, zero_add, mul_zero, Pi.add_apply] using (ht.add hl).add hg

/-- Uniform absolute approximation to the genuine signed root torus integral. -/
theorem torus_integral_approx (F : EdgeSet (n+1)) (hm : 64 ≤ n+1)
    (hb : UniformTorusTail.beta (n+1) < 1)
    (hc : LocalLogCos.cutoff (n+1) ≤ Real.pi/8) :
    ‖torusIntegral F - (quarticConstant*Z (n+1) 1*gaussianFactor F : ℝ)‖ ≤
      errorEnvelope (n+1)*Z (n+1) 1 := by
  let r := LocalLogCos.cutoff (n+1)
  let U := ∫ x in rootCube n r, torusIntegrand F x
  let V := ∫ x in rootCube n r, phaseKernel (rootMatrix F) (rootImbalance F) x
  let J := ∫ x, phaseKernel (rootMatrix F) (rootImbalance F) x
  have hm8 : 8 ≤ n+1 := by omega
  have hr : 0 ≤ r := LocalLogCos.cutoff_nonneg _
  have ht := torus_tail_bound F r (by dsimp [r]; linarith [Real.pi_pos])
  have hl := local_integral_bound F (by omega) r hr hc
  have hg := phase_tail_bound F hm8 r hr
  have htb := UniformTorusTail.normalized_tailEnvelope_bound (graph F) (graph_degree_le_two F) hm hb (1/16)
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  rw [← cutoff_eq_window] at htb
  have htab := (div_le_iff₀ hz).mp htb
  have hta : UniformTorusTail.tailIntegral (graph F) r ≤
      |UniformTorusTail.tailEnvelope (n+1) (1/16)| * Z (n+1) 1 := by
    exact htab.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  rw [LocalLogCos.errorBudget_cutoff _ (by omega)] at hl
  have hln := (normalization_comparison F hm8).2
  have hcoef : 0 ≤ LocalLogCos.cutoffError (n+1)+ForestQuartic.errorRate (n+1) := by
    unfold LocalLogCos.cutoffError ForestQuartic.errorRate; positivity
  have hlocal := hl.trans (mul_le_mul_of_nonneg_left hln hcoef)
  have he : torusIntegral F-(quarticConstant:ℂ)*J =
      (torusIntegral F-U)+(U-(quarticConstant:ℂ)*V)+(quarticConstant:ℂ)*(V-J) := by ring
  have hn : ‖torusIntegral F-(quarticConstant:ℂ)*J‖ ≤
      ‖torusIntegral F-U‖ + ‖U-(quarticConstant:ℂ)*V‖ + quarticConstant*‖V-J‖ := by
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos quarticConstant_pos]
    exact add_le_add (norm_add_le (torusIntegral F-U) (U-(quarticConstant:ℂ)*V)) le_rfl
  have htotal := hn.trans (add_le_add (add_le_add (ht.trans hta) hlocal)
    (mul_le_mul_of_nonneg_left hg quarticConstant_pos.le))
  have hJ : J=(Z (n+1) 1*gaussianFactor F:ℝ) := phase_integral_eq F hm8
  rw [hJ, ← Complex.ofReal_mul] at htotal
  simpa only [errorEnvelope, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using htotal

lemma torus_real_approx (F : EdgeSet (n+1)) (hm : 64 ≤ n+1)
    (hb : UniformTorusTail.beta (n+1) < 1)
    (hc : LocalLogCos.cutoff (n+1) ≤ Real.pi/8) :
    |(torusIntegral F).re-quarticConstant*Z (n+1) 1*gaussianFactor F| ≤
      errorEnvelope (n+1)*Z (n+1) 1 := by
  have h := Complex.abs_re_le_norm
    (torusIntegral F-(quarticConstant*Z (n+1) 1*gaussianFactor F:ℝ))
  exact h.trans (torus_integral_approx F hm hb hc)

end RegularContainment
