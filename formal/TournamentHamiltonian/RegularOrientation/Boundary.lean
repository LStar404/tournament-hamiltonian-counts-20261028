module

public import TournamentHamiltonian.RegularOrientation.Regular

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup MvPolynomial
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Nonempty regular tournaments necessarily have odd order; the empty type is
excluded explicitly rather than silently treated as an odd-order graph. -/
theorem regular_order_odd {m : ℕ} (hm : 0 < m) (T : Tournament m) (hT : IsRegular T) : Odd m := by
  let i : Fin m := ⟨0, hm⟩
  have hi := hT i
  rw [score_eq_outDegree] at hi
  have he : (2 : ℝ) * outDegree T i + 1 = m := by linarith
  have hn : 2 * outDegree T i + 1 = m := by exact_mod_cast he
  exact ⟨outDegree T i, hn.symm⟩

theorem no_regular_positive_even {m : ℕ} (hm : 0 < m) (he : Even m) :
    ¬ Nonempty (RegularTournament m) := by
  rintro ⟨T⟩
  exact (Nat.not_odd_iff_even.mpr he) (regular_order_odd hm T.val T.property)

/-- Exact requested coefficient quotient, displayed with a forced-tail monomial
prefactor and the product over the remaining unordered edges. -/
theorem regularProbability_eq_deleted_product {k : ℕ} (s : Finset (Edge (2*k+1)))
    (a : Orientation (2*k+1)) :
    regularProbability s a =
      (((∏ e ∈ s, (X (winner a e) : MvPolynomial (Fin (2*k+1)) ℕ)) *
        ∏ e ∈ sᶜ, (X e.val.1 + X e.val.2)).coeff (regularExponent k) : ℝ) /
          (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  rw [regularProbability_eq_coeff_ratio, constrainedPolynomial_factorization]

theorem regularProbability_bounds {k : ℕ} (s : Finset (Edge (2*k+1)))
    (a : Orientation (2*k+1)) :
    0 ≤ regularProbability s a ∧ regularProbability s a ≤ 1 := by
  have hd : (0 : ℝ) < Fintype.card (RegularTournament (2*k+1)) := by
    exact_mod_cast regular_card_pos k
  unfold regularProbability
  constructor
  · positivity
  · apply (div_le_one hd).mpr
    exact_mod_cast (Finset.card_le_univ
      (Finset.univ.filter (fun T : RegularTournament (2*k+1) => Contains T.val s a)))

end
end RegularOrientation
