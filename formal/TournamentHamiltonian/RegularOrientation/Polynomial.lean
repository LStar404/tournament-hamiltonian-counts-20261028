module

public import TournamentHamiltonian.RegularOrientation.Degrees

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup MvPolynomial
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual winner generating polynomial, with natural-number coefficients. -/
def orientationPolynomial (m : ℕ) : MvPolynomial (Fin m) ℕ :=
  ∏ e : Edge m, (X e.val.1 + X e.val.2)

theorem prod_winner_X {m : ℕ} (ω : Orientation m) :
    (∏ e : Edge m, X (winner ω e) : MvPolynomial (Fin m) ℕ) =
      monomial (winnerExponent ω) 1 := by
  simpa only [winnerExponent, X] using
    (monomial_sum_one (R := ℕ) Finset.univ (fun e : Edge m => Finsupp.single (winner ω e) 1)).symm

theorem orientationPolynomial_eq_sum_bits (m : ℕ) :
    orientationPolynomial m = ∑ ω : Orientation m, monomial (winnerExponent ω) 1 := by
  have he : ∀ e : Edge m, (X e.val.1 + X e.val.2 : MvPolynomial (Fin m) ℕ) =
      ∑ b : Bool, X (if b then e.val.1 else e.val.2) := by
    intro e
    simp [Fintype.univ_bool]
  simp only [orientationPolynomial, he]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact prod_winner_X ω

/-- Complete generating-function identity indexed by actual labelled tournaments. -/
theorem orientationPolynomial_eq_sum_tournaments (m : ℕ) :
    orientationPolynomial m = ∑ T : Tournament m, monomial (outVector T) 1 := by
  rw [orientationPolynomial_eq_sum_bits]
  apply Fintype.sum_equiv (tournamentEquiv m)
  intro ω
  rw [winnerExponent_eq_outVector]
  rfl

/-- Every coefficient is exactly the number of labelled tournaments with that
outdegree vector, not an assumed coefficient-count correspondence. -/
theorem orientationPolynomial_coeff (m : ℕ) (r : Exponent m) :
    (orientationPolynomial m).coeff r =
      (Finset.univ.filter (fun T : Tournament m => outVector T = r)).card := by
  rw [orientationPolynomial_eq_sum_tournaments, coeff_sum]
  simp_rw [coeff_monomial]
  simp

end
end RegularOrientation
