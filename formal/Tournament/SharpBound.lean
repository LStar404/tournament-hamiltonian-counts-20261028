module

public import Tournament.PathConvolution
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The sharp quantitative endpoint and the genuine finite maximum

`TournamentHamiltonian.MainBound` retains the older upper constant C_*.
The separate `SharpMainBound` below uses cosh(1)/cos(1) on both sides.
It specifies the endpoint proved in `TournamentHamiltonian.SharpMain`.
The theorems here identify its maximum with actual Hamilton orderings and
justify taking a uniform upper bound through the finite maximum.
-/

@[expose] public section

namespace TournamentPaths

/-- Preserve every Boolean edge when returning from the legacy representation. -/
def fromLegacy {n : ℕ} (T : TournamentHamiltonian.Tournament n) : Tournament (Fin n) where
  edge := T.val
  loopless := T.property.1
  oriented := T.property.2

def tournamentEquivLegacy (n : ℕ) :
    Tournament (Fin n) ≃ TournamentHamiltonian.Tournament n where
  toFun := toLegacy
  invFun := fromLegacy
  left_inv T := by cases T; rfl
  right_inv T := by cases T; rfl

noncomputable instance finiteTournaments (n : ℕ) : Fintype (Tournament (Fin n)) :=
  Fintype.ofEquiv (TournamentHamiltonian.Tournament n) (tournamentEquivLegacy n).symm

/-- The maximum of the manuscript's actual ordering count over all tournaments. -/
noncomputable def maxPathCountFinite (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (pathCountFinite (n := n))

theorem pathCountFinite_le_maxPathCountFinite {n : ℕ} (T : Tournament (Fin n)) :
    pathCountFinite T ≤ maxPathCountFinite n := by
  classical
  exact Finset.le_sup (Finset.mem_univ T)

/-- The finite maximum is exactly the legacy P(n), with no analytic hypothesis. -/
theorem maxPathCountFinite_eq_legacy (n : ℕ) :
    maxPathCountFinite n = TournamentHamiltonian.maxPaths n := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro T _
    rw [pathCountFinite_eq_legacy]
    exact TournamentHamiltonian.pathCount_le_maxPaths (toLegacy T)
  · apply Finset.sup_le
    intro T _
    have h := pathCountFinite_le_maxPathCountFinite (fromLegacy T)
    simpa only [pathCountFinite_eq_legacy, fromLegacy, toLegacy] using h

/-- Uniform bounds pass to the finite maximum without interchanging limits. -/
theorem maxPathCountFinite_le_real_iff (n : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    (maxPathCountFinite n : ℝ) ≤ b ↔
      ∀ T : Tournament (Fin n), (pathCountFinite T : ℝ) ≤ b := by
  constructor
  · intro h T
    exact (Nat.cast_le.mpr (pathCountFinite_le_maxPathCountFinite T)).trans h
  · classical
    intro h
    unfold maxPathCountFinite
    have hsup : ∀ s : Finset (Tournament (Fin n)),
        ((s.sup pathCountFinite : ℕ) : ℝ) ≤ b := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hb
      | @insert T s hT ih =>
        rw [Finset.sup_insert, Nat.cast_max]
        exact max_le (h T) ih
    exact hsup Finset.univ

end TournamentPaths

namespace TournamentHamiltonian

/-- The requested sharp two-sided O(1/n) endpoint; this is not the old MainBound. -/
def SharpMainBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (lowerConstant - K / n) * meanPaths n ≤ (maxPaths n : ℝ) ∧
    (maxPaths n : ℝ) ≤ (lowerConstant + K / n) * meanPaths n

/-- Exact rewriting of the sharp endpoint using the current genuine path count. -/
theorem sharpMainBound_iff_current_maximum : SharpMainBound ↔
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (lowerConstant - K / n) * meanPaths n ≤
        (TournamentPaths.maxPathCountFinite n : ℝ) ∧
      (TournamentPaths.maxPathCountFinite n : ℝ) ≤
        (lowerConstant + K / n) * meanPaths n := by
  simp only [SharpMainBound, TournamentPaths.maxPathCountFinite_eq_legacy]

/-- The manuscript's multiplicative bounds equal the normalized absolute error. -/
theorem sharpMainBound_iff_normalized_error : SharpMainBound ↔
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      |(maxPaths n : ℝ) / meanPaths n - lowerConstant| ≤ K / n := by
  constructor
  · rintro ⟨K, hK, N, hN, h⟩
    refine ⟨K, hK, N, hN, ?_⟩
    intro n hn
    have hm : 0 < meanPaths n := by unfold meanPaths; positivity
    have hl := (le_div_iff₀ hm).mpr (h n hn).1
    have hu := (div_le_iff₀ hm).mpr (h n hn).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨K, hK, N, hN, h⟩
    refine ⟨K, hK, N, hN, ?_⟩
    intro n hn
    have hm : 0 < meanPaths n := by unfold meanPaths; positivity
    have he := abs_le.mp (h n hn)
    exact ⟨(le_div_iff₀ hm).mp (by linarith [he.1]),
      (div_le_iff₀ hm).mp (by linarith [he.2])⟩

end TournamentHamiltonian
