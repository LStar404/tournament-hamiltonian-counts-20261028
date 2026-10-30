module

public import TournamentHamiltonian.RegularFourier.Characters
public import TournamentHamiltonian.RegularOrientation.Regular

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def evaluation {m : ℕ} (p : MvPolynomial (Fin m) ℕ) (x : Fin m → ℝ) : ℂ :=
  eval₂ (Nat.castRingHom ℂ) (fun i => Complex.exp ((2*x i : ℝ)*Complex.I)) p

def centeredEvaluation {m : ℕ} (r : Exponent m) (p : MvPolynomial (Fin m) ℕ)
    (x : Fin m → ℝ) : ℂ :=
  Complex.exp ((-2*(∑ i, (r i : ℝ)*x i) : ℝ)*Complex.I) * evaluation p x

lemma evaluation_monomial {m : ℕ} (d : Exponent m) (c : ℕ) (x : Fin m → ℝ) :
    evaluation (monomial d c) x =
      (c : ℂ)*Complex.exp ((2*(∑ i, (d i : ℝ)*x i) : ℝ)*Complex.I) := by
  rw [evaluation, eval₂_monomial, Finsupp.prod_fintype _ _ (by simp)]
  congr 1
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma centered_monomial {m : ℕ} (r d : Exponent m) (c : ℕ) (x : Fin m → ℝ) :
    centeredEvaluation r (monomial d c) x =
      (c : ℂ)*character (fun i => (d i : ℤ)-(r i : ℤ)) x := by
  rw [centeredEvaluation, evaluation_monomial, character_sum, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

lemma difference_zero_iff {m : ℕ} (r d : Exponent m) :
    (fun i => (d i : ℤ)-(r i : ℤ)) = 0 ↔ d=r := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at hi
    exact hi
  · rintro rfl
    funext i
    simp

lemma centered_expansion {m : ℕ} (r : Exponent m) (p : MvPolynomial (Fin m) ℕ)
    (x : Fin m → ℝ) :
    centeredEvaluation r p x =
      ∑ d ∈ p.support, (p.coeff d : ℂ)*character (fun i => (d i : ℤ)-(r i : ℤ)) x := by
  conv_lhs => rw [p.as_sum]
  simp only [centeredEvaluation, evaluation, eval₂_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simpa only [centeredEvaluation, evaluation, Finset.mul_sum] using centered_monomial r d (p.coeff d) x

/-- Exact finite coefficient extraction on a length-π Lebesgue box, using frequency 2.
There is no normalized Haar measure and no asymptotic input. -/
theorem coefficient_integral {m : ℕ} (a : ℝ) (r : Exponent m)
    (p : MvPolynomial (Fin m) ℕ) :
    (∫ x, centeredEvaluation r p x ∂boxMeasure m a) =
      (p.coeff r : ℂ)*(Real.pi : ℂ)^m := by
  simp_rw [centered_expansion]
  rw [integral_finsetSum _ (fun d _ => (character_integrable _ a).const_mul _)]
  simp_rw [integral_const_mul, integral_character, difference_zero_iff]
  rw [Finset.sum_eq_single r]
  · simp
  · intro d _ hdr
    simp [hdr]
  · intro hr
    have hz : p.coeff r=0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using hr
    simp [hz]

lemma centered_periodic {m : ℕ} (r : Exponent m) (p : MvPolynomial (Fin m) ℕ) :
    complexPeriodic (centeredEvaluation r p) := by
  intro x i
  simp_rw [centered_expansion]
  apply Finset.sum_congr rfl
  intro d _
  rw [character_periodic _ x i]
end RegularFourier
