module

public import Tournament.StochasticZero.Core
public import TournamentHamiltonian.Definitions

set_option autoImplicit false
open scoped BigOperators Matrix

@[expose] public section

namespace StochasticZero
open TournamentHamiltonian

/-- The lazy tournament transition matrix `(2/n)(A + I/2)`. -/
noncomputable def lazyTournament {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (2 / (n : ℝ)) * (adjacency T i j + if i = j then 1 / 2 else 0)

/-- A regular tournament has directed diameter at most two (apart from the
trivial zero-length path). This proves connectivity from regularity. -/
theorem regular_tournament_diameter_two {n : ℕ} (T : Tournament n)
    (hreg : ∀ i, ∑ j, adjacency T i j = ((n : ℝ) - 1) / 2)
    (i j : Fin n) (hij : i ≠ j) :
    T.val i j = true ∨ ∃ k, T.val i k = true ∧ T.val k j = true := by
  classical
  by_cases hedge : T.val i j = true
  · exact Or.inl hedge
  right
  by_contra hno
  have hji : T.val j i = true := by
    have hpair := T.property.2 i j hij
    cases h : T.val j i <;> simp_all
  have hle : ∀ k, adjacency T i k ≤ adjacency T j k := by
    intro k
    by_cases hik : T.val i k = true
    · have hkj : T.val k j ≠ true := fun h => hno ⟨k, hik, h⟩
      have hkjne : k ≠ j := by intro heq; subst k; exact hedge hik
      have hjk : T.val j k = true := by
        have hpair := T.property.2 k j hkjne
        cases h : T.val j k <;> simp_all
      simp [adjacency, hik, hjk]
    · simp only [adjacency, hik, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> norm_num
  have hstrict : adjacency T i i < adjacency T j i := by
    simp [adjacency, T.property.1, hji]
  have hsumlt := Finset.sum_lt_sum (fun k _ => hle k)
    ⟨i, Finset.mem_univ i, hstrict⟩
  rw [hreg i, hreg j] at hsumlt
  exact lt_irrefl _ hsumlt

/-- Positive tournament edges remain positive in the lazy transition. -/
theorem lazyTournament_edge_pos {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (i j : Fin n) (hij : T.val i j = true) : 0 < lazyTournament T i j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [lazyTournament, adjacency]
  simp only [hij, ↓reduceIte]
  split_ifs <;> positivity

/-- Regularity supplies actual reachability, not an extra irreducibility hypothesis. -/
theorem lazyTournament_reachable {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (hreg : ∀ i, ∑ j, adjacency T i j = ((n : ℝ) - 1) / 2) :
    ∀ i j, PositiveReachable (lazyTournament T) i j := by
  intro i j
  by_cases hij : i = j
  · subst j; exact Relation.ReflTransGen.refl
  rcases regular_tournament_diameter_two T hreg i j hij with he | ⟨k, hik, hkj⟩
  · exact Relation.ReflTransGen.single (lazyTournament_edge_pos T hn i j he)
  · exact (Relation.ReflTransGen.single (r := fun a b => 0 < lazyTournament T a b)
      (lazyTournament_edge_pos T hn i k hik)).tail
      (lazyTournament_edge_pos T hn k j hkj)

/-- All stochastic hypotheses for the actual lazy regular-tournament matrix. -/
theorem lazyTournament_stochastic {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (hreg : ∀ i, ∑ j, adjacency T i j = ((n : ℝ) - 1) / 2) :
    (∀ i j, 0 ≤ lazyTournament T i j) ∧
    (∀ i, ∑ j, lazyTournament T i j = 1) ∧
    (∀ i, 0 < lazyTournament T i i) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp [lazyTournament, adjacency]
    split_ifs <;> positivity
  · intro i
    simp only [lazyTournament, ← Finset.mul_sum, Finset.sum_add_distrib, hreg]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    field_simp
    ring
  · intro i
    simp only [lazyTournament, adjacency, T.property.1, Bool.false_eq_true, ↓reduceIte,
      zero_add]
    positivity

/-- Exact finite zero set for the concrete lazy transition of a regular tournament. -/
theorem regular_tournament_zero_locus {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (hreg : ∀ i, ∑ j, adjacency T i j = ((n : ℝ) - 1) / 2)
    (u : Fin n → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1) :
    (twistedMatrix (lazyTournament T) u).det = 0 ↔ ∀ j, u j = 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hp, hsum, hdiag⟩ := lazyTournament_stochastic T hn hreg
  exact det_twistedMatrix_eq_zero_iff (lazyTournament T) u hp hsum hdiag
    (lazyTournament_reachable T hn hreg) hu

end StochasticZero
