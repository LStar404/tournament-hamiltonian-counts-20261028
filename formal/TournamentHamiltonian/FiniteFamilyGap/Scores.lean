module

public import TournamentHamiltonian.SpectralSupplement.QuantitativeGap
public import TournamentHamiltonian.BaseRelabel.Expectations

@[expose] public section

set_option autoImplicit false
namespace FiniteFamilyGap
open TournamentHamiltonian TournamentHamiltonian.Equality RegularOrientation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The ordinary carousel isomorphism class, not the larger signed-switching class. -/
def CarouselClass (h : ℕ) (T : Tournament (2*h+1)) : Prop :=
  ∃ e : Equiv.Perm (Fin (2*h+1)), relabelTournament T e = carouselTournament h

/-- The actual piecewise expression for the uniform limiting score. Nonregular
bases have score zero, even when they share the maximal spectral ratio. -/
def uniformScore {d : ℕ} (T : Tournament d) : ℝ :=
  if IsRegular T then spectralRatio T else 0

/-- The regular-block limiting expression. This definition does not assert a
limit theorem; its actual expectation-limit identification is a separate obligation. -/
def regularScore {d : ℕ} (T : Tournament d) : ℝ :=
  Real.exp (1/(d:ℝ)) * uniformScore T

theorem carousel_class_self (h : ℕ) : CarouselClass h (carouselTournament h) := by
  refine ⟨Equiv.refl _, ?_⟩
  rfl

theorem regular_of_carouselClass {h : ℕ} {T : Tournament (2*h+1)}
    (hT : CarouselClass h T) : IsRegular T := by
  obtain ⟨e, he⟩ := hT
  intro i
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [← score_relabelTournament T e j, he]
  exact carouselTournament_score h j

theorem uniformScore_of_regular {d : ℕ} (T : Tournament d) (hT : IsRegular T) :
    uniformScore T = spectralRatio T := ite_eq_left hT

theorem uniformScore_of_nonregular {d : ℕ} (T : Tournament d) (hT : ¬IsRegular T) :
    uniformScore T = 0 := ite_eq_right hT

theorem regularScore_of_nonregular {d : ℕ} (T : Tournament d) (hT : ¬IsRegular T) :
    regularScore T = 0 := by simp [regularScore, uniformScore, hT]

theorem uniformScore_carousel (h : ℕ) :
    uniformScore (carouselTournament h) = spectralRatio (carouselTournament h) :=
  uniformScore_of_regular _ (carouselTournament_score h)

theorem uniformScore_carousel_pos (h : ℕ) : 0 < uniformScore (carouselTournament h) := by
  rw [uniformScore_carousel]
  exact actual_spectralRatio_pos _ (by omega)

theorem regularScore_carousel_pos (h : ℕ) : 0 < regularScore (carouselTournament h) :=
  mul_pos (Real.exp_pos _) (uniformScore_carousel_pos h)

theorem uniformScore_eq_of_carouselClass {h : ℕ} {T : Tournament (2*h+1)}
    (hT : CarouselClass h T) : uniformScore T = uniformScore (carouselTournament h) := by
  rw [uniformScore_of_regular T (regular_of_carouselClass hT), uniformScore_carousel]
  exact (regular_spectralRatio_eq_carousel_iff_relabel h T (regular_of_carouselClass hT)).mpr hT

theorem regularScore_eq_of_carouselClass {h : ℕ} {T : Tournament (2*h+1)}
    (hT : CarouselClass h T) : regularScore T = regularScore (carouselTournament h) := by
  simp only [regularScore, uniformScore_eq_of_carouselClass hT]

/-- A genuine positive gap valid at every odd base order. No finite minimum
or assumed strict gap is needed: this reuses the proved sixth-moment loss. -/
def spectralGap (h : ℕ) : ℝ :=
  spectralRatio (carouselTournament h) *
    (1 - Real.exp (-(16 / (3 * ((2*h+1:ℕ):ℝ)^6))))

theorem spectralGap_pos (h : ℕ) : 0 < spectralGap h := by
  apply mul_pos (actual_spectralRatio_pos _ (by omega))
  have hd : (0:ℝ) < (2*h+1:ℕ) := by positivity
  have he : Real.exp (-(16 / (3 * ((2*h+1:ℕ):ℝ)^6))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  linarith

theorem spectralGap_le_carousel (h : ℕ) : spectralGap h ≤ uniformScore (carouselTournament h) := by
  rw [uniformScore_carousel]
  unfold spectralGap
  have hp := actual_spectralRatio_pos (carouselTournament h) (by omega)
  have he := Real.exp_pos (-(16 / (3 * ((2*h+1:ℕ):ℝ)^6)))
  nlinarith

/-- Crucial two-branch gap: nonregular scores are zero, not their spectral ratios. -/
theorem spectralGap_le_uniform_deficit (h : ℕ) (T : Tournament (2*h+1))
    (hT : ¬CarouselClass h T) :
    spectralGap h ≤ uniformScore (carouselTournament h) - uniformScore T := by
  by_cases hr : IsRegular T
  · rw [uniformScore_of_regular T hr, uniformScore_carousel]
    exact (regular_noncarousel_quantitative_spectral_gap h T hr hT).2.2.1
  · rw [uniformScore_of_nonregular T hr, sub_zero]
    exact spectralGap_le_carousel h

theorem uniformScore_lt_iff_not_carouselClass (h : ℕ) (T : Tournament (2*h+1)) :
    uniformScore T < uniformScore (carouselTournament h) ↔ ¬CarouselClass h T := by
  constructor
  · intro hlt he
    exact (ne_of_lt hlt) (uniformScore_eq_of_carouselClass he)
  · intro he
    have := spectralGap_le_uniform_deficit h T he
    have := spectralGap_pos h
    linarith

theorem uniformScore_eq_iff_carouselClass (h : ℕ) (T : Tournament (2*h+1)) :
    uniformScore T = uniformScore (carouselTournament h) ↔ CarouselClass h T := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_lt ((uniformScore_lt_iff_not_carouselClass h T).mpr hn)) he
  · exact uniformScore_eq_of_carouselClass

theorem uniformScore_le_carousel (h : ℕ) (T : Tournament (2*h+1)) :
    uniformScore T ≤ uniformScore (carouselTournament h) := by
  by_cases hc : CarouselClass h T
  · exact (uniformScore_eq_of_carouselClass hc).le
  · exact ((uniformScore_lt_iff_not_carouselClass h T).mpr hc).le

theorem regularScore_lt_iff_not_carouselClass (h : ℕ) (T : Tournament (2*h+1)) :
    regularScore T < regularScore (carouselTournament h) ↔ ¬CarouselClass h T := by
  rw [regularScore, regularScore, mul_lt_mul_iff_right₀ (Real.exp_pos _)]
  exact uniformScore_lt_iff_not_carouselClass h T

theorem regularScore_eq_iff_carouselClass (h : ℕ) (T : Tournament (2*h+1)) :
    regularScore T = regularScore (carouselTournament h) ↔ CarouselClass h T := by
  rw [regularScore, regularScore, mul_right_inj' (Real.exp_ne_zero _)]
  exact uniformScore_eq_iff_carouselClass h T

theorem regularScore_le_carousel (h : ℕ) (T : Tournament (2*h+1)) :
    regularScore T ≤ regularScore (carouselTournament h) :=
  mul_le_mul_of_nonneg_left (uniformScore_le_carousel h T) (Real.exp_pos _).le

end
end FiniteFamilyGap
