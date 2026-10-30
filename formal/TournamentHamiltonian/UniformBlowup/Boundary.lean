module

public import TournamentHamiltonian.UniformBlowup.Normalization
public import TournamentHamiltonian.UniformBlowup.Marginal

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian Equiv.Perm
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Block size one is a valid deterministic model, not an empty sample space. -/
theorem sample_card_blocksize_one (d : ℕ) : Fintype.card (Sample d 1) = 1 := by
  rw [card_sample]
  simp

/-- With singleton blocks the sampled graph is exactly the base graph under
projection of the redundant singleton coordinate. -/
theorem arc_blocksize_one {d : ℕ} (T : Tournament d) (ω : Sample d 1)
    (u v : Vertex d 1) : arc T ω u v = T.val u.1 v.1 := by
  by_cases hb : u.1 = v.1
  · have huv : u = v := Prod.ext hb (Subsingleton.elim _ _)
    subst v
    simp [T.property.1]
  · simp [arc, hb]

def baseOne : Tournament 1 :=
  ⟨fun _ _ => false, ⟨fun _ => rfl,
    fun _i _j h => False.elim (h (Subsingleton.elim _ _))⟩⟩

def twoCycle : Cycle 1 2 :=
  ⟨Equiv.swap ((0,0) : Vertex 1 2) (0,1),
    ⟨Equiv.Perm.isCycle_swap (by decide), by
      rw [Equiv.Perm.support_swap (by decide)]
      decide⟩⟩

/-- Concrete failure at N=2: the two required arcs demand opposite values
of the same single Boolean coordinate. -/
theorem twoCycle_impossible (ω : Sample 1 2) : ¬ IsCyclePresent baseOne ω twoCycle := by
  intro h
  have h01 : arc baseOne ω ((0,0) : Vertex 1 2) (0,1) = true := by
    simpa [twoCycle] using h ((0,0) : Vertex 1 2)
  have h10 : arc baseOne ω ((0,1) : Vertex 1 2) (0,0) = true := by
    simpa [twoCycle] using h ((0,1) : Vertex 1 2)
  have hr := arc_reverse baseOne ω ((0,0) : Vertex 1 2) (0,1) (by decide)
  rw [h01, h10] at hr
  contradiction

theorem twoCycle_probability_zero :
    ((Finset.univ.filter (fun ω : Sample 1 2 => IsCyclePresent baseOne ω twoCycle)).card : ℝ) /
      Fintype.card (Sample 1 2) = 0 := by
  simp [twoCycle_impossible]

theorem twoCycle_weight_quarter : cycleWeight baseOne twoCycle = (1/4 : ℝ) := by
  have he : ∀ u : Vertex 1 2, weight baseOne u (twoCycle.val u) = (1/2 : ℝ) := by
    intro u
    simp only [weight, ite_eq_right (cycle_ne_self twoCycle u).symm,
      ite_eq_left (Subsingleton.elim u.1 (twoCycle.val u).1)]
  simp only [cycleWeight, he, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- The N≥3 hypothesis in the cycle probability theorem cannot be dropped. -/
theorem twoCycle_probability_ne_weight :
    ((Finset.univ.filter (fun ω : Sample 1 2 => IsCyclePresent baseOne ω twoCycle)).card : ℝ) /
      Fintype.card (Sample 1 2) ≠ cycleWeight baseOne twoCycle := by
  rw [twoCycle_probability_zero, twoCycle_weight_quarter]
  norm_num

end
end UniformBlowup
