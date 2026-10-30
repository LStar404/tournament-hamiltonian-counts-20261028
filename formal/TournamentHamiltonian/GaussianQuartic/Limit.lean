module

public import TournamentHamiltonian.GaussianQuartic.Moments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section

theorem exp_neg_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have ordered {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
      |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
    have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
    have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 0 ≤ 1 - Real.exp (a-b) := by
      have := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hab)
      linarith
    have h3 := Real.add_one_le_exp (a-b)
    have heq : Real.exp (-b) = Real.exp (-a) * Real.exp (a-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [abs_of_nonneg (sub_nonneg.mpr he), abs_of_nonpos (sub_nonpos.mpr hab), heq]
    calc
      Real.exp (-a) - Real.exp (-a) * Real.exp (a-b) =
          Real.exp (-a) * (1 - Real.exp (a-b)) := by ring
      _ ≤ 1 * (1 - Real.exp (a-b)) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ -(a-b) := by linarith
  rcases le_total a b with hab | hba
  · exact ordered ha hab
  · rw [abs_sub_comm (Real.exp (-a)) _, abs_sub_comm a b]
    exact ordered hb hba

theorem integral_abs_le_sqrt_second {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    (∫ z, |g z| ∂μ) ≤ Real.sqrt (∫ z, g z ^ 2 ∂μ) := by
  have h := variance_nonneg (fun z => |g z|) μ
  have ha : MemLp (fun z => |g z|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  rw [variance_eq_sub ha] at h
  simp only [Pi.pow_apply, sq_abs] at h
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem quartic_measurable (m : ℕ) : Measurable (quartic m) := by
  unfold quartic unorderedSum edge4
  fun_prop

def expDeviation (m : ℕ) (z : Fin m → ℝ) : ℝ :=
  |Real.exp (-quartic m z) - Real.exp (-(1/2 : ℝ))|

theorem expDeviation_bound (m : ℕ) (z : Fin m → ℝ) :
    expDeviation m z ≤ |quartic m z - 1/2| :=
  exp_neg_lipschitz (quartic_nonneg m z) (by norm_num)

theorem expDeviation_integrable (m : ℕ) :
    Integrable (expDeviation m) (gaussian (Fin m)) := by
  have h : Integrable (fun z => |quartic m z - 1/2|) (gaussian (Fin m)) :=
    ((quartic_integrable m).sub (integrable_const _)).abs
  apply h.mono'
  · have hq := quartic_measurable m
    have he : Measurable (fun z => Real.exp (-quartic m z) - Real.exp (-(1/2 : ℝ))) := by
      fun_prop
    change AEStronglyMeasurable (fun z => |Real.exp (-quartic m z) - Real.exp (-(1/2 : ℝ))|) _
    simpa only [Real.norm_eq_abs] using he.norm.aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs, expDeviation, abs_abs] using expDeviation_bound m z)

theorem expDeviation_L2_bound (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, expDeviation m z ∂gaussian (Fin m)) ≤
      Real.sqrt ((26 * (m : ℝ)^2 - 11*m - 12) / (12*(m : ℝ)^3)) := by
  calc
    _ ≤ ∫ z, |quartic m z - 1/2| ∂gaussian (Fin m) :=
      integral_mono (expDeviation_integrable m)
        ((quartic_integrable m).sub (integrable_const _)).abs (expDeviation_bound m)
    _ ≤ Real.sqrt (∫ z, (quartic m z - 1/2)^2 ∂gaussian (Fin m)) :=
      integral_abs_le_sqrt_second _ ((quartic_memLp_two m).sub (memLp_const _))
    _ = _ := by rw [quartic_deviation_second m hm]

theorem expDeviation_rate (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, expDeviation m z ∂gaussian (Fin m)) ≤ Real.sqrt (3 / (m : ℝ)) := by
  apply (expDeviation_L2_bound m hm).trans
  apply Real.sqrt_le_sqrt
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 12 * (m : ℝ)^3)).2
  field_simp
  nlinarith [sq_nonneg (m : ℝ)]

/-- Dimensions may vary with m: this is convergence of the real expectation sequence. -/
theorem expDeviation_tendsto :
    Tendsto (fun m : ℕ => ∫ z, expDeviation m z ∂gaussian (Fin m)) atTop (𝓝 0) := by
  have hr : Tendsto (fun m : ℕ => Real.sqrt (3 / (m : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
    have hs := h.sqrt
    simpa only [mul_zero, Real.sqrt_zero, mul_one_div] using hs
  apply squeeze_zero' (Eventually.of_forall (fun m => integral_nonneg (fun z => abs_nonneg _)))
    _ hr
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact expDeviation_rate m hm

/-- Unfolded expectation endpoint over a genuinely different product Gaussian space at each m. -/
theorem quartic_exp_L1_tendsto :
    Tendsto (fun m : ℕ => ∫ z : Fin m → ℝ,
      |Real.exp (-quartic m z) - Real.exp (-(1/2 : ℝ))| ∂Measure.pi (fun _ => gaussianReal 0 1))
      atTop (𝓝 0) := expDeviation_tendsto

end
end GaussianQuartic
