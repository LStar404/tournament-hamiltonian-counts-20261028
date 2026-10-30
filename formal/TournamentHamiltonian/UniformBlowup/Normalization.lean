module

public import TournamentHamiltonian.UniformBlowup.ExistingPathCount
public import TournamentHamiltonian.UniformBlowup.Cycle
public import Mathlib.GroupTheory.Perm.Centralizer

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian Equiv.Perm
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Consecutive-position pairs are exactly the `N-1` path steps. -/
def stepEquiv (n : ℕ) : Step n ≃ Fin (n-1) where
  toFun r := ⟨r.val.1.val, by have := r.val.2.isLt; have := r.property; omega⟩
  invFun i := ⟨(⟨i.val, by have := i.isLt; omega⟩,
    ⟨i.val + 1, by have := i.isLt; omega⟩), rfl⟩
  left_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext rfl
    · exact Fin.ext r.property.symm
  right_inv i := rfl

theorem card_step (n : ℕ) : Fintype.card (Step n) = n-1 := by
  rw [Fintype.card_congr (stepEquiv n), Fintype.card_fin]

def vertexEquiv (d m : ℕ) : Arrangement d m :=
  Fintype.equivOfCardEq (by simp)

theorem card_arrangement (d m : ℕ) : Fintype.card (Arrangement d m) = (d*m).factorial := by
  simpa using Fintype.card_equiv (vertexEquiv d m)

theorem fullCycle_iff_cycleType {d m : ℕ} (σ : Equiv.Perm (Vertex d m)) :
    (σ.IsCycle ∧ σ.support = Finset.univ) ↔ σ.cycleType = {d*m} := by
  constructor
  · rintro ⟨hc, hs⟩
    rw [hc.cycleType, hs]
    simp
  · intro h
    have hc : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by simp [h])
    refine ⟨hc, ?_⟩
    have hs : σ.support.card = d*m := by
      simpa only [hc.cycleType, Multiset.singleton_inj] using h
    apply Finset.eq_univ_of_card
    simpa using hs

/-- Exact unrooted cycle normalization: one successor permutation per directed
cycle, and exactly `(N-1)!` possible full cycles before arc constraints. -/
theorem card_cycle {d m : ℕ} (hN : 2 ≤ d*m) :
    Fintype.card (Cycle d m) = (d*m-1).factorial := by
  rw [Fintype.card_subtype]
  simp_rw [fullCycle_iff_cycleType]
  simpa using (Equiv.Perm.card_of_cycleType_singleton (α := Vertex d m)
    hN (by simp))

theorem b_one_block {m : ℕ} (π : Arrangement 1 m) : b π = m-1 := by
  rw [b_eq_card_internalStep, Fintype.card_subtype]
  have h : ∀ r : Step (1*m), (tail π r).1 = (head π r).1 := fun _ => Subsingleton.elim _ _
  simp only [h, Finset.filter_true, Finset.card_univ, card_step, Nat.one_mul]

/-- The one-block model recovers exactly μ_N = N! / 2^(N-1), including N = 0,1. -/
theorem avgPath_one_block (m : ℕ) (T : Tournament 1) :
    avgPath (m := m) T = (m.factorial : ℝ) / 2^(m-1) := by
  rw [avgPath_eq_weightedPathSum]
  have hw : ∀ π : Arrangement 1 m, pathWeight T π = (1/2 : ℝ)^(m-1) := by
    intro π
    have hc : Compatible T π := fun _ h => False.elim (h (Subsingleton.elim _ _))
    rw [pathWeight_eq, ite_eq_left hc, b_one_block]
  simp only [weightedPathSum, hw, Finset.sum_const, Finset.card_univ,
    card_arrangement, Nat.one_mul, nsmul_eq_mul, one_div_pow, mul_one_div]

/-- The one-block cycle model recovers ν_N = (N-1)! / 2^N with no missing N factor. -/
theorem avgCycle_one_block (m : ℕ) (hm : 3 ≤ m) (T : Tournament 1) :
    avgCycle (m := m) T = ((m-1).factorial : ℝ) / 2^m := by
  have hN : 3 ≤ 1*m := by simpa using hm
  rw [avgCycle_eq_weightedCycleSum hN]
  have hw : ∀ σ : Cycle 1 m, cycleWeight T σ = (1/2 : ℝ)^m := by
    intro σ
    have he : ∀ u : Vertex 1 m, weight T u (σ.val u) = (1/2 : ℝ) := by
      intro u
      simp only [weight, ite_eq_right (cycle_ne_self σ u).symm,
        ite_eq_left (Subsingleton.elim u.1 (σ.val u).1)]
    simp only [cycleWeight, he, Finset.prod_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Nat.one_mul]
  simp only [weightedCycleSum, hw, Finset.sum_const, Finset.card_univ,
    card_cycle (by omega : 2 ≤ 1*m), Nat.one_mul, nsmul_eq_mul, one_div_pow, mul_one_div]

end
end UniformBlowup
