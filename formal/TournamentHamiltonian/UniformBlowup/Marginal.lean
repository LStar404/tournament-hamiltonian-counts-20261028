module

public import TournamentHamiltonian.UniformBlowup.Expectation

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every matrix entry is itself the exact expected adjacency indicator. -/
theorem expected_arc_eq_weight {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    (∑ ω : Sample d m, if arc T ω u v = true then (1 : ℝ) else 0) /
      Fintype.card (Sample d m) = weight T u v := by
  classical
  by_cases huv : u = v
  · subst v
    simp [weight]
  by_cases hb : u.1 = v.1
  · have hi : u.2 ≠ v.2 := fun h => huv (Prod.ext hb h)
    let c : Coord d m := (u.1, edgeOf u.2 v.2 hi)
    let a : Coord d m → Bool := fun _ => decide (u.2 < v.2)
    have he (ω : Sample d m) : arc T ω u v = true ↔ ω c = a c := by
      simp only [arc, ite_eq_left hb, internalArc, dite_eq_right hi]
      dsimp [c, a]
      by_cases hl : u.2 < v.2 <;> simp [hl]
    have hcard : (Finset.univ.filter (fun ω : Sample d m => arc T ω u v = true)).card =
        2 ^ (d * m.choose 2 - 1) := by
      simp_rw [he]
      simpa only [Finset.mem_singleton, forall_eq, card_coord, Finset.card_singleton]
        using fixed_filter_card {c} a
    have hpos : 1 ≤ d * m.choose 2 := by
      rw [← card_coord]
      exact Fintype.card_pos_iff.mpr ⟨c⟩
    rw [Finset.sum_boole, hcard, card_sample]
    simp only [Nat.cast_pow, Nat.cast_ofNat, weight, ite_eq_right huv, ite_eq_left hb]
    simpa using pow_sub_div (d * m.choose 2) 1 hpos
  · by_cases ha : T.val u.1 v.1 = true
    · simp [arc, hb, ha, weight, huv]
    · simp [arc, hb, ha, weight, huv]

/-- Entrywise form of the manuscript matrix `(J-I+S⊗J_m)/2`. -/
theorem weight_eq_block_formula {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    weight T u v = (1 - (if u = v then (1 : ℝ) else 0) +
      TournamentHamiltonian.signMatrix T u.1 v.1) / 2 := by
  by_cases huv : u = v
  · subst v
    simp [weight, TournamentHamiltonian.signMatrix]
  by_cases hb : u.1 = v.1
  · simp [weight, huv, hb, TournamentHamiltonian.signMatrix]
  · cases ha : T.val u.1 v.1 <;>
      norm_num [weight, huv, hb, ha, TournamentHamiltonian.signMatrix]

end
end UniformBlowup
