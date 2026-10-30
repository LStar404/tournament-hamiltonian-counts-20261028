module

public import TournamentHamiltonian.UniformBlowup.Model

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Each block is an actual labelled tournament. -/
def internalTournament {m : ℕ} (ω : Edge m → Bool) : Tournament m :=
  ⟨internalArc ω, ⟨internalArc_self ω, internalArc_reverse ω⟩⟩

def tournamentBits {m : ℕ} (T : Tournament m) : Edge m → Bool :=
  fun e => T.val e.val.1 e.val.2

theorem internalArc_tournamentBits {m : ℕ} (T : Tournament m) (i j : Fin m) :
    internalArc (tournamentBits T) i j = T.val i j := by
  by_cases hij : i = j
  · subst j
    simp [T.property.1]
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · simp [internalArc, hij, hijlt, tournamentBits, edgeOf,
      min_eq_left hijlt.le, max_eq_right hijlt.le]
  · simp only [internalArc, dite_eq_right hij, ite_eq_right (not_lt_of_ge hjilt.le)]
    simpa [tournamentBits, edgeOf, min_eq_right hjilt.le, max_eq_left hjilt.le]
      using (T.property.2 i j hij).symm

/-- Boolean edge coordinates are in bijection with *all* labelled tournaments;
there are no duplicate samples or inaccessible internal tournaments. -/
def tournamentEquiv (m : ℕ) : (Edge m → Bool) ≃ Tournament m where
  toFun := internalTournament
  invFun := tournamentBits
  left_inv ω := by
    funext e
    have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    have he : edgeOf e.val.1 e.val.2 hne = e := by
      apply Subtype.ext
      simp [edgeOf, min_eq_left e.property.le, max_eq_right e.property.le]
    simp [tournamentBits, internalTournament, internalArc, hne, e.property, he]
  right_inv T := by
    apply Subtype.ext
    funext i j
    exact internalArc_tournamentBits T i j

/-- The global cube is the product of one copy of all labelled tournaments per
block. Uniform counting through this bijection is exactly independent uniform
internal blocks. -/
def blockTournamentEquiv (d m : ℕ) : Sample d m ≃ (Fin d → Tournament m) where
  toFun ω i := tournamentEquiv m (fun e => ω (i,e))
  invFun blocks c := (tournamentEquiv m).symm (blocks c.1) c.2
  left_inv ω := by
    funext c
    exact congrFun ((tournamentEquiv m).left_inv (fun e => ω (c.1,e))) c.2
  right_inv blocks := by
    funext i
    exact (tournamentEquiv m).right_inv (blocks i)

/-- The block-product equivalence uses exactly the internal arcs of `blowup`. -/
theorem arc_same_block {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (i : Fin d) (a b : Fin m) :
    arc T ω (i,a) (i,b) = ((blockTournamentEquiv d m ω) i).val a b := by
  simp [arc, blockTournamentEquiv, tournamentEquiv, internalTournament]

/-- Change of variables for any block statistic: the cube's equal-weight average
is precisely the equal-weight average over the Cartesian product of all labelled
internal tournaments. -/
theorem average_eq_uniform_blocks {d m : ℕ} (f : (Fin d → Tournament m) → ℝ) :
    (∑ ω : Sample d m, f (blockTournamentEquiv d m ω)) / Fintype.card (Sample d m) =
      (∑ blocks : Fin d → Tournament m, f blocks) / Fintype.card (Fin d → Tournament m) := by
  rw [Fintype.sum_equiv (blockTournamentEquiv d m) _ f (fun _ => rfl),
    Fintype.card_congr (blockTournamentEquiv d m)]

theorem internal_tournament_card (m : ℕ) :
    Fintype.card (Tournament m) = 2 ^ m.choose 2 := by
  rw [← Fintype.card_congr (tournamentEquiv m), Fintype.card_fun, Fintype.card_bool, card_edge]

end
end UniformBlowup
