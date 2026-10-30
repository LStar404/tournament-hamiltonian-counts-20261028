module

public import TournamentHamiltonian.BlockRatio.Decomposition
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Filter Topology
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The block size runs through all natural numbers; eventual statements remove small sizes. -/
theorem eventually_order_ge (d K : ℕ) (hd : 0 < d) : ∀ᶠ m : ℕ in atTop, K ≤ d * m := by
  filter_upwards [eventually_ge_atTop K] with m hm
  nlinarith

theorem blockStep_tendsto_zero {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => blockStep d m) atTop (𝓝 0) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : Tendsto (fun m : ℕ => (d : ℝ) * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hdR
  have ht : Tendsto (fun m : ℕ => (d : ℝ) * (m : ℝ) - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [ha.eventually_ge_atTop (b + 1)] with m hm
    linarith
  simpa only [blockStep, Nat.cast_mul] using tendsto_const_nhds.div_atTop ht

theorem mul_blockStep_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => (m : ℝ) * blockStep d m) atTop (𝓝 ((1 : ℝ) / d)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun m : ℕ => 1 / ((d : ℝ) - 1 / m)) atTop (𝓝 (1 / ((d : ℝ) - 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub hi) (by simpa only [sub_zero] using hdR)
  apply (show Tendsto (fun m : ℕ => 1 / ((d : ℝ) - 1 / m)) atTop (𝓝 (1 / (d : ℝ))) by
    simpa only [sub_zero] using ht).congr' 
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [blockStep, Nat.cast_mul]
  field_simp

/-- The logarithm is used only where its actual scalar factors are positive. -/
theorem log_scalarRatio {d m : ℕ} (hN : 3 ≤ d * m) :
    Real.log (scalarRatio d m) = Real.log (1 + blockStep d m) -
      Real.log (1 - blockStep d m ^ 2) / 2 := by
  have ha : 0 < 1 + blockStep d m := by linarith [blockStep_pos (by omega : 2 ≤ d * m)]
  rw [scalarRatio, Real.log_div ha.ne' (scalar_sqrt_pos hN).ne',
    Real.log_sqrt (scalar_gram_pos hN).le]

/-- The scalar correction itself tends to one. -/
theorem scalarRatio_tendsto_one {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => scalarRatio d m) atTop (𝓝 1) := by
  have h0 := blockStep_tendsto_zero hd
  have hs : Tendsto (fun m : ℕ => Real.sqrt (1 - blockStep d m ^ 2)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.tendsto (1 - (0 : ℝ) ^ 2) |>.comp
      (tendsto_const_nhds.sub (h0.pow 2))
  have ht : Tendsto ((fun m : ℕ => 1 + blockStep d m) /
      (fun m : ℕ => Real.sqrt (1 - blockStep d m ^ 2))) atTop (𝓝 1) := by
    simpa only [add_zero, div_one] using
      (tendsto_const_nhds.add h0).div hs (by norm_num : (1 : ℝ) ≠ 0)
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem log_scalarRatio_tendsto_zero {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => Real.log (scalarRatio d m)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (scalarRatio_tendsto_one hd)

/-- The first-order logarithmic correction is exactly `1/d`. -/
theorem mul_log_scalarRatio_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => (m : ℝ) * Real.log (scalarRatio d m)) atTop (𝓝 ((1 : ℝ) / d)) := by
  have hplus := Real.tendsto_nat_mul_log_one_add_of_tendsto (mul_blockStep_tendsto hd)
  have hsq : Tendsto (fun m : ℕ => (m : ℝ) * (-(blockStep d m ^ 2))) atTop (𝓝 0) := by
    have ht := ((mul_blockStep_tendsto hd).mul (blockStep_tendsto_zero hd)).neg
    simp only [mul_zero, neg_zero] at ht
    convert ht using 1
    funext m
    ring
  have hminus := Real.tendsto_nat_mul_log_one_add_of_tendsto hsq
  have ht := hplus.sub (hminus.div_const 2)
  simp only [zero_div, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_order_ge d 3 hd] with m hm
  rw [log_scalarRatio hm]
  simp only [sub_eq_add_neg]
  ring

/-- The scalar block multiplicity tends to e. Division removes the base constant direction;
`d*m-d` remains a natural exponent, and only eventual nonempty block sizes are used. -/
theorem scalarRatio_power_div_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => scalarRatio d m ^ (d * m - d) / scalarRatio d m)
      atTop (𝓝 (Real.exp 1)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hl : Tendsto (fun m : ℕ => (d : ℝ) * ((m : ℝ) * Real.log (scalarRatio d m)) -
      ((d : ℝ) + 1) * Real.log (scalarRatio d m)) atTop (𝓝 1) := by
    simpa [hdR] using ((mul_log_scalarRatio_tendsto hd).const_mul (d : ℝ)).sub
      ((log_scalarRatio_tendsto_zero hd).const_mul ((d : ℝ) + 1))
  apply ((Real.continuous_exp.tendsto 1).comp hl).congr'
  filter_upwards [eventually_order_ge d 3 hd, eventually_ge_atTop 1] with m hm hm1
  have hdim : d ≤ d * m := by nlinarith
  have hp := scalarRatio_pos hm
  have hquot : 0 < scalarRatio d m ^ (d * m - d) / scalarRatio d m :=
    div_pos (pow_pos hp _) hp
  rw [← Real.exp_log hquot, Real.log_div (pow_ne_zero _ hp.ne') hp.ne', Real.log_pow,
    Nat.cast_sub hdim, Nat.cast_mul]
  change Real.exp _ = Real.exp _
  congr 1
  ring_nf

end
end UniformBlockMatrix
