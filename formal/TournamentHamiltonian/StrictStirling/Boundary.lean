module

public import TournamentHamiltonian.StrictStirling.Bounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace StrictStirling

lemma theta_zero : theta 0=0 := by simp [theta]
lemma zero_is_excluded : ¬(0<theta 0) := by rw [theta_zero]; exact lt_irrefl _

lemma theta_one : theta 1=12-6*Real.log (2*Real.pi) := by
  norm_num [theta]
  ring

lemma theta_one_strict : 0<12-6*Real.log (2*Real.pi) ∧ 12-6*Real.log (2*Real.pi)<1 := by
  simpa only [theta_one] using theta_bounds 1 (by norm_num)

lemma theta_two_strict : 0<theta 2 ∧ theta 2<1 := theta_bounds 2 (by norm_num)

lemma step_first_term_equal (r : ℝ) :
    (1:ℝ)/(2*((0+1:ℕ):ℝ)+1)*r^(0+1) = r^(0+1)/3 := by norm_num; ring

lemma step_second_term_strict (r : ℝ) (hr : 0<r) :
    (1:ℝ)/(2*((1+1:ℕ):ℝ)+1)*r^(1+1) < r^(1+1)/3 := by
  norm_num
  nlinarith [sq_pos_of_pos hr]

lemma factorial_one_exact : (1:ℝ)=Real.sqrt (2*Real.pi)/Real.exp 1 *
    Real.exp ((12-6*Real.log (2*Real.pi))/12) := by
  simpa only [Nat.factorial_one, Nat.cast_one, mul_one, one_mul, one_div, pow_one, theta_one,
    div_eq_mul_inv] using factorial_eq 1 (by norm_num)

end StrictStirling
