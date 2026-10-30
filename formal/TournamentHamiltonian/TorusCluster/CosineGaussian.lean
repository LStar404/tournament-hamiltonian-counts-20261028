module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open Set

lemma cos_le_gaussian_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb : b < Real.pi/2) :
    Real.cos b ≤ Real.exp (-(b^2/2)) := by
  let f : ℝ → ℝ := fun t => Real.exp (t^2/2)*Real.cos t
  have hd (t : ℝ) : HasDerivAt f
      (Real.exp (t^2/2)*(t*Real.cos t-Real.sin t)) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2).exp.mul (Real.hasDerivAt_cos t) using 1
    · rfl
    · dsimp; ring
  have hanti : AntitoneOn f (Icc 0 b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · dsimp [f]; fun_prop
    · intro t _; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht'.1, Real.pi_pos], lt_of_le_of_lt ht'.2 hb⟩
      have htan := Real.le_tan ht'.1 (lt_of_le_of_lt ht'.2 hb)
      rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at htan
      rw [(hd t).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr htan)
  have hf := hanti ⟨le_rfl,hb0⟩ ⟨hb0,le_rfl⟩ hb0
  have hf' : Real.cos b * Real.exp (b^2/2) ≤ 1 := by simpa [f, mul_comm] using hf
  have hdiv := (le_div_iff₀ (Real.exp_pos (b^2/2))).mpr hf'
  simpa [Real.exp_neg, one_div] using hdiv

/-- Complete local cosine Gaussian bound, including both endpoints. No logarithm
or division by a potentially zero cosine occurs in the final theorem. -/
theorem abs_cos_le_gaussian {u : ℝ} (hu : |u| ≤ Real.pi/2) :
    |Real.cos u| ≤ Real.exp (-(u^2/2)) := by
  have hnon : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc (abs_le.mp hu)
  rw [abs_of_nonneg hnon]
  rcases eq_or_lt_of_le hu with he | hl
  · have hz : Real.cos u = 0 := by rw [← Real.cos_abs, he, Real.cos_pi_div_two]
    rw [hz]
    exact (Real.exp_pos _).le
  · have hb := cos_le_gaussian_nonneg (abs_nonneg u) hl
    simpa only [Real.cos_abs, sq_abs] using hb

end
end TorusCluster
