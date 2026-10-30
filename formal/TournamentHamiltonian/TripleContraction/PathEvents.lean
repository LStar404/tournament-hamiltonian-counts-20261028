module

public import TournamentHamiltonian.TripleContraction.Principal
public import TournamentHamiltonian.TripleContraction.PathBridge

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle FixedDeletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

def someDeleted (U : Finset α) : Finset (Option α) := U.map Function.Embedding.some

/-- Actual complement after deletion of old vertices, keeping the sentinel. -/
def sentinelComplementEquiv (U : Finset α) :
    ((someDeleted U)ᶜ : Finset (Option α)) ≃ Option (Uᶜ : Finset α) where
  toFun x := by
    rcases x with ⟨x,hx⟩
    cases x with
    | none => exact none
    | some a => exact some ⟨a,by
        simpa only [someDeleted,Finset.mem_compl,Finset.mem_map,
          Function.Embedding.some_apply,Option.some.injEq,exists_eq_right] using hx⟩
  invFun x := match x with
    | none => ⟨none,by simp [someDeleted]⟩
    | some a => ⟨some a.val,by
        simpa only [someDeleted,Finset.mem_compl,Finset.mem_map,
          Function.Embedding.some_apply,Option.some.injEq,exists_eq_right] using a.property⟩
  left_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem sentinel_principal_matrix (A : Matrix α α ℝ) (U : Finset α) :
    principal (sentinel A) (someDeleted U) =
      (sentinel (principal A U)).submatrix (sentinelComplementEquiv U) (sentinelComplementEquiv U) := by
  ext x y
  rcases x with ⟨x,hx⟩
  rcases y with ⟨y,hy⟩
  cases x <;> cases y <;> rfl

theorem sentinel_principal_cyc (A : Matrix α α ℝ) (U : Finset α) :
    cyc (principal (sentinel A) (someDeleted U))=path (principal A U) := by
  let : Nonempty ((someDeleted U)ᶜ : Finset (Option α)) := ⟨⟨none,by simp [someDeleted]⟩⟩
  rw [sentinel_principal_matrix,UniformFinalScalars.cyc_submatrix_equiv,sentinel_cyc_eq_path]

namespace Triple
variable (t s : Triple α)
def some : Triple (Option α) where
  first := Option.some t.first
  middle := Option.some t.middle
  last := Option.some t.last
  first_middle := fun h => t.first_middle (Option.some.inj h)
  first_last := fun h => t.first_last (Option.some.inj h)
  middle_last := fun h => t.middle_last (Option.some.inj h)

omit [Fintype α] in
@[simp] theorem some_deleted : t.some.deleted=someDeleted t.deleted := by
  simp [some,deleted,someDeleted]
omit [Fintype α] in
@[simp] theorem some_doubleDeleted : t.some.doubleDeleted s.some=someDeleted (t.doubleDeleted s) := by
  simp [doubleDeleted,someDeleted,Finset.map_union]

omit [Fintype α] [DecidableEq α] in
theorem separated_some (h : t.Separated s) : t.some.Separated s.some := by
  intro x hx
  cases x with
  | none => simp [some] at hx
  | some x =>
    have hx' : x=s.first ∨ x=s.middle ∨ x=s.last := by simpa [some] using hx
    simpa [some] using h x hx'

def PathHolds (π : Ordering α) : Prop :=
  PathArc π t.first t.middle ∧ PathArc π t.middle t.last

theorem pathHolds_iff (π : Ordering α) :
    t.PathHolds π ↔ t.some.Holds (orderingCycleEquiv π).val := by
  unfold PathHolds Holds some
  rw [orderingCycleEquiv_arc,orderingCycleEquiv_arc]

end Triple

omit [Fintype α] [DecidableEq α] in
theorem rowTwins_sentinel (A : Matrix α α ℝ) {u v : α} (h : RowTwins A u v) :
    RowTwins (sentinel A) (some u) (some v) := by
  intro x hx hy
  cases x with
  | none => simp
  | some x => exact h x (fun he => hx (congrArg some he)) (fun he => hy (congrArg some he))

/-- Actual ordering event sum, without a probability denominator. -/
def pathEvent (A : Matrix α α ℝ) (P : Ordering α → Prop) : ℝ :=
  ∑ π : Ordering α, if P π then pathMonomial A π else 0

theorem pathEvent_eq_cycleEvent (A : Matrix α α ℝ) (P : Ordering α → Prop)
    (Q : Equiv.Perm (Option α) → Prop) (h : ∀ π, P π ↔ Q (orderingCycleEquiv π).val) :
    pathEvent A P=cycleEvent (sentinel A) Q := by
  unfold pathEvent cycleEvent
  apply Fintype.sum_equiv orderingCycleEquiv
  intro π
  rw [← h π,orderingCycleEquiv_monomial]

/-- The genuine principal path completion is in bijection with actual orderings
containing the triple, including the singleton completion. -/
def principalTriplePathEquiv (t : Triple α) :
    Ordering (t.deletedᶜ : Finset α) ≃ {π : Ordering α // t.PathHolds π} :=
  let ec : (t.some.deletedᶜ : Finset (Option α)) ≃ Option (t.deletedᶜ : Finset α) := by
    simpa only [t.some_deleted] using sentinelComplementEquiv t.deleted
  let ee := orderingCycleEquiv.subtypeEquiv (fun π => t.pathHolds_iff π)
  orderingCycleEquiv |>.trans ((fullCongr ec.symm).trans
    ((principalTripleCycleEquiv t.some).trans ee.symm))

def principalDoublePathEquiv (t s : Triple α) (h : t.Separated s) :
    Ordering ((t.doubleDeleted s)ᶜ : Finset α) ≃
      {π : Ordering α // t.PathHolds π ∧ s.PathHolds π} :=
  let ec : ((t.some.doubleDeleted s.some)ᶜ : Finset (Option α)) ≃
      Option ((t.doubleDeleted s)ᶜ : Finset α) := by
    simpa only [t.some_doubleDeleted s] using sentinelComplementEquiv (t.doubleDeleted s)
  let ee := orderingCycleEquiv.subtypeEquiv
    (fun π => and_congr (t.pathHolds_iff π) (s.pathHolds_iff π))
  orderingCycleEquiv |>.trans ((fullCongr ec.symm).trans
    ((principalDoubleCycleEquiv t.some s.some (t.separated_some s h)).trans ee.symm))

/-- Exact triple path sum. N=3 leaves one true edge-free completion. -/
theorem path_triple (A : Matrix α α ℝ) (t : Triple α)
    (hmid : RowTwins A t.first t.middle) (hlast : RowTwins A t.first t.last)
    (hn : 3 ≤ Fintype.card α) :
    pathEvent A t.PathHolds=(A t.first t.middle*A t.first t.last)*path (principal A t.deleted) := by
  have hc : 2 ≤ Fintype.card t.some.Kept := by
    rw [Triple.kept_card,Fintype.card_option]
    omega
  rw [pathEvent_eq_cycleEvent A t.PathHolds t.some.Holds (fun π => t.pathHolds_iff π),
    cycle_triple (sentinel A) t.some (rowTwins_sentinel A hmid) (rowTwins_sentinel A hlast) hc,
    t.some_deleted,sentinel_principal_cyc]
  rfl

/-- Exact two disjoint triple path sum; both triples may occupy the same block. -/
theorem path_double (A : Matrix α α ℝ) (t s : Triple α) (h : t.Separated s)
    (htm : RowTwins A t.first t.middle) (htl : RowTwins A t.first t.last)
    (hsm : RowTwins A s.first s.middle) (hsl : RowTwins A s.first s.last)
    (hn : 6 ≤ Fintype.card α) :
    pathEvent A (fun π => t.PathHolds π ∧ s.PathHolds π)=
      (A t.first t.middle*A t.first t.last)*(A s.first s.middle*A s.first s.last)*
        path (principal A (t.doubleDeleted s)) := by
  have hc : 2 ≤ Fintype.card (t.some.lift s.some (t.separated_some s h)).Kept := by
    rw [Triple.doubleKept_card,Fintype.card_option]
    omega
  rw [pathEvent_eq_cycleEvent A _ (fun σ => t.some.Holds σ ∧ s.some.Holds σ)
      (fun π => and_congr (t.pathHolds_iff π) (s.pathHolds_iff π)),
    cycle_double (sentinel A) t.some s.some (t.separated_some s h)
      (rowTwins_sentinel A htm) (rowTwins_sentinel A htl)
      (rowTwins_sentinel A hsm) (rowTwins_sentinel A hsl) hc,
    t.some_doubleDeleted s,sentinel_principal_cyc]
  rfl

end
end TripleContraction
