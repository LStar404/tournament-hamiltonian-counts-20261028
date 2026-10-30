module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace TournamentHamiltonian

/-- The exact derivative in Appendix A.7. -/
theorem hasDerivAt_tan_sub_cubic {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.tan y - y - y ^ 3 / 3)
      (Real.tan x ^ 2 - x ^ 2) x := by
  have hd : HasDerivAt (fun y : ℝ => Real.tan y - y - y ^ 3 / 3)
      (1 / Real.cos x ^ 2 - 1 - (3 * x ^ 2) / 3) x := by
    simpa using! ((Real.hasDerivAt_tan hx).sub (hasDerivAt_id x)).sub
      ((hasDerivAt_pow 3 x).div_const 3)
  convert hd using 1
  have hi := Real.one_add_tan_sq_mul_cos_sq_eq_one hx
  field_simp [hx]
  nlinarith

/-- Appendix A.7, with only the stated domain assumptions. -/
theorem tan_ge_self_add_cube_div_three {y : ℝ} (hy : 0 ≤ y) (hyp : y < Real.pi / 2) :
    y + y ^ 3 / 3 ≤ Real.tan y := by
  have hd (x : ℝ) (hx : x ∈ Set.Ico 0 (Real.pi / 2)) :=
    hasDerivAt_tan_sub_cubic (Real.cos_pos_of_mem_Ioo
      (show x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)).ne'
  have hmono : MonotoneOn (fun x : ℝ => Real.tan x - x - x ^ 3 / 3)
      (Set.Ico 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 (Real.pi / 2))
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ico 0 (Real.pi / 2) := interior_subset hx
      rw [(hd x hx').deriv]
      have ht := Real.le_tan hx'.1 hx'.2
      have htp : 0 ≤ Real.tan x := hx'.1.trans ht
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (add_nonneg htp hx'.1)]
  have hz : (0 : ℝ) ∈ Set.Ico 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hh := hmono hz ⟨hy, hyp⟩ hy
  simp only [Real.tan_zero, zero_sub, sub_zero] at hh
  linarith

end TournamentHamiltonian
