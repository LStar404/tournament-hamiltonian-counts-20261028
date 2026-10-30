module

public import TournamentHamiltonian.RegularOrientation.Constraints

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup MvPolynomial
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Genuine regular labelled tournaments, using the manuscript's signed score. -/
def IsRegular {m : ℕ} (T : Tournament m) : Prop := ∀ i, score T i = 0
abbrev RegularTournament (m : ℕ) := {T : Tournament m // IsRegular T}

def regularExponent (k : ℕ) : Exponent (2*k+1) :=
  Finsupp.equivFunOnFinite.symm (fun _ => k)

theorem regular_iff_outVector {k : ℕ} (T : Tournament (2*k+1)) :
    IsRegular T ↔ outVector T = regularExponent k := by
  constructor
  · intro h
    ext i
    change outDegree T i = k
    have hi := h i
    rw [score_eq_outDegree] at hi
    have he : (outDegree T i : ℝ) = k := by
      push_cast at hi
      linarith
    exact_mod_cast he
  · intro h i
    have hi := congrArg (fun r : Exponent (2*k+1) => r i) h
    change outDegree T i = k at hi
    rw [score_eq_outDegree, hi]
    push_cast
    ring

/-- An explicit carousel witnesses nonemptiness at every odd order, including one. -/
def regularCarousel (k : ℕ) : RegularTournament (2*k+1) :=
  ⟨carouselTournament k, carouselTournament_score k⟩

theorem regular_card_pos (k : ℕ) : 0 < Fintype.card (RegularTournament (2*k+1)) :=
  Fintype.card_pos_iff.mpr ⟨regularCarousel k⟩

theorem regular_card_eq_coeff (k : ℕ) :
    Fintype.card (RegularTournament (2*k+1)) =
      (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  rw [orientationPolynomial_coeff, Fintype.card_subtype]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, regular_iff_outVector]

theorem regular_coefficient_pos (k : ℕ) :
    0 < (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  rw [← regular_card_eq_coeff]
  exact regular_card_pos k

/-- A true uniform regular-tournament event, defined only at odd orders whose
sample space has already been proved nonempty. This is not independent edge sampling. -/
def regularProbability {k : ℕ} (s : Finset (Edge (2*k+1))) (a : Orientation (2*k+1)) : ℝ :=
  ((Finset.univ.filter (fun T : RegularTournament (2*k+1) => Contains T.val s a)).card : ℝ) /
    Fintype.card (RegularTournament (2*k+1))

def regularContainedEquiv {k : ℕ} (s : Finset (Edge (2*k+1))) (a : Orientation (2*k+1)) :
    {T : RegularTournament (2*k+1) // Contains T.val s a} ≃
      {T : Tournament (2*k+1) // Contains T s a ∧ outVector T = regularExponent k} where
  toFun T := ⟨T.val.val, T.property, (regular_iff_outVector T.val.val).mp T.val.property⟩
  invFun T := ⟨⟨T.val, (regular_iff_outVector T.val).mpr T.property.2⟩, T.property.1⟩
  left_inv _T := rfl
  right_inv _T := rfl

theorem regular_contained_card_eq_coeff {k : ℕ} (s : Finset (Edge (2*k+1)))
    (a : Orientation (2*k+1)) :
    (Finset.univ.filter (fun T : RegularTournament (2*k+1) => Contains T.val s a)).card =
      (constrainedPolynomial s a).coeff (regularExponent k) := by
  rw [constrainedPolynomial_coeff]
  have h := Fintype.card_congr (regularContainedEquiv s a)
  simpa only [Fintype.card_subtype] using h

/-- Exact regular containment probability as a quotient of actual polynomial
coefficients. Its denominator is strictly positive by `regular_coefficient_pos`.
No independence, forest asymptotic, or local-limit estimate is assumed. -/
theorem regularProbability_eq_coeff_ratio {k : ℕ} (s : Finset (Edge (2*k+1)))
    (a : Orientation (2*k+1)) :
    regularProbability s a =
      ((constrainedPolynomial s a).coeff (regularExponent k) : ℝ) /
        (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  rw [regularProbability, regular_contained_card_eq_coeff, regular_card_eq_coeff]

/-- The denominator is nonzero after casting to the field used for probabilities. -/
theorem regular_denominator_pos (k : ℕ) :
    (0 : ℝ) < (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  exact_mod_cast regular_coefficient_pos k

end
end RegularOrientation
