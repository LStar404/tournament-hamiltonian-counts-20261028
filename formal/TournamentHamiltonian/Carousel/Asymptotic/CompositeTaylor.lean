module
public import TournamentHamiltonian.Carousel.Asymptotic.RealFormBridge
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology
set_option backward.isDefEq.respectTransparency false

/-- The quadratic cosh expansion is derived from global smoothness, not assumed. -/
theorem cosh_one_quadratic_remainder :
    (fun y : ℝ => Real.cosh y - (Real.cosh 1 + Real.sinh 1*(y-1) +
      Real.cosh 1/2*(y-1)^2)) =O[𝓝 1] (fun y => (y-1)^3) := by
  have ht := (taylor_isLittleO_univ (f := Real.cosh) (x₀ := 1) (n := 3)
    Real.contDiff_cosh).isBigO
  have h3 := (isBigO_refl (fun y : ℝ => (y-1)^3) (𝓝 1)).const_mul_left (Real.sinh 1/6)
  convert ht.add h3 using 1
  funext y
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ]
  ring

/-- The quadratic cosine expansion is derived from global smoothness. -/
theorem cos_one_quadratic_remainder :
    (fun y : ℝ => Real.cos y - (Real.cos 1 - Real.sin 1*(y-1) -
      Real.cos 1/2*(y-1)^2)) =O[𝓝 1] (fun y => (y-1)^3) := by
  have ht := (taylor_isLittleO_univ (f := Real.cos) (x₀ := 1) (n := 3)
    Real.contDiff_cos).isBigO
  have h3 := (isBigO_refl (fun y : ℝ => (y-1)^3) (𝓝 1)).const_mul_left (Real.sin 1/6)
  convert ht.add h3 using 1
  funext y
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ]
  ring

/-- The linear exponential expansion with an actual quadratic Big-O remainder. -/
theorem exp_zero_linear_remainder :
    (fun y : ℝ => Real.exp y - (1+y)) =O[𝓝 0] (fun y => y^2) := by
  simpa [Finset.sum_range_succ] using Real.exp_sub_sum_range_isBigO_pow 2

end TournamentHamiltonian
