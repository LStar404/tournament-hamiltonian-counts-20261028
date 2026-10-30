module

public import Tournament.SmallScoreApproximation
public import Tournament.SignMatrix
public import TournamentHamiltonian.Equality.SpectralClassification

set_option autoImplicit false

@[expose] public section

namespace TournamentPaths

/-- Ordinary relabelling of the current Boolean tournament, preserving every edge. -/
def relabelFiniteTournament {n : ℕ} (T : Tournament (Fin n)) (e : Equiv.Perm (Fin n)) :
    Tournament (Fin n) where
  edge := fun i j => T.edge (e i) (e j)
  loopless := fun i => T.loopless (e i)
  oriented := fun i j hij => T.oriented (e i) (e j) (fun h => hij (e.injective h))

def alternatingFiniteTournament (n : ℕ) : Tournament (Fin n) :=
  fromLegacy (TournamentHamiltonian.alternatingTournament n)

def carouselFiniteTournament (m : ℕ) : Tournament (Fin (2 * m + 1)) :=
  fromLegacy (TournamentHamiltonian.carouselTournament m)

@[simp] theorem toLegacy_fromLegacy {n : ℕ} (T : TournamentHamiltonian.Tournament n) :
    toLegacy (fromLegacy T) = T := rfl

@[simp] theorem toLegacy_relabelFiniteTournament {n : ℕ} (T : Tournament (Fin n))
    (e : Equiv.Perm (Fin n)) :
    toLegacy (relabelFiniteTournament T e) = TournamentHamiltonian.relabelTournament (toLegacy T) e := rfl

/-- Genuine-current-type classification, at every order including 0 and 1. -/
theorem pathSpectralRatio_eq_iff_signedPermutationTransitive {n : ℕ} (T : Tournament (Fin n)) :
    pathSpectralRatio T = pathSpectralRatio (alternatingFiniteTournament n) ↔
      TournamentHamiltonian.Equality.SignedPermutationTransitive (signMatrix T) := by
  simpa only [pathSpectralRatio, alternatingFiniteTournament, toLegacy_fromLegacy,
    signMatrix_toLegacy] using
    TournamentHamiltonian.Equality.spectralRatio_eq_iff_signedPermutationTransitive (toLegacy T)

theorem pathSpectralRatio_lt_iff_not_signedPermutationTransitive {n : ℕ} (T : Tournament (Fin n)) :
    pathSpectralRatio T < pathSpectralRatio (alternatingFiniteTournament n) ↔
      ¬ TournamentHamiltonian.Equality.SignedPermutationTransitive (signMatrix T) := by
  simpa only [pathSpectralRatio, alternatingFiniteTournament, toLegacy_fromLegacy,
    signMatrix_toLegacy] using
    TournamentHamiltonian.Equality.spectralRatio_lt_iff_not_signedPermutationTransitive (toLegacy T)

/-- The sixth-moment gap for the manuscript's actual current sign matrix. -/
theorem signMatrix_sixth_moment_gap_sixteen {n : ℕ} (T : Tournament (Fin n))
    (hT : ¬ TournamentHamiltonian.Equality.SignedPermutationTransitive (signMatrix T)) :
    16 ≤ TournamentHamiltonian.matrixFrobSq
        ((TournamentHamiltonian.transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 3) -
      TournamentHamiltonian.matrixFrobSq ((signMatrix T) ^ 3) := by
  simpa only [signMatrix_toLegacy] using
    TournamentHamiltonian.Equality.sixth_moment_gap_sixteen_of_not_signedPermutationTransitive
      (toLegacy T) (by simpa only [signMatrix_toLegacy] using hT)

theorem regular_toLegacy_score_zero {n : ℕ} (T : Tournament (Fin n)) (hT : IsRegular T) :
    ∀ i, TournamentHamiltonian.score (toLegacy T) i = 0 := by
  intro i
  rw [score_toLegacy]
  have h := congrFun (regular_signMatrix_mulVec_one T hT) i
  simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] using h

/-- Ordinary carousel isomorphism uses a vertex permutation only, never a sign
switching. Regularity is the current finite outdegree predicate. -/
theorem regular_pathSpectralRatio_eq_carousel_iff_relabel (m : ℕ)
    (T : Tournament (Fin (2 * m + 1))) (hT : IsRegular T) :
    pathSpectralRatio T = pathSpectralRatio (carouselFiniteTournament m) ↔
      ∃ e : Equiv.Perm (Fin (2 * m + 1)), relabelFiniteTournament T e = carouselFiniteTournament m := by
  have h := TournamentHamiltonian.Equality.regular_spectralRatio_eq_carousel_iff_relabel m
    (toLegacy T) (regular_toLegacy_score_zero T hT)
  change TournamentHamiltonian.spectralRatio (toLegacy T) =
      TournamentHamiltonian.spectralRatio (TournamentHamiltonian.carouselTournament m) ↔ _
  rw [h]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    apply (tournamentEquivLegacy (2 * m + 1)).injective
    change toLegacy (relabelFiniteTournament T e) = toLegacy (carouselFiniteTournament m)
    simpa only [toLegacy_relabelFiniteTournament, carouselFiniteTournament, toLegacy_fromLegacy] using he
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have h' := congrArg toLegacy he
    simpa only [toLegacy_relabelFiniteTournament, carouselFiniteTournament, toLegacy_fromLegacy] using h'

end TournamentPaths
