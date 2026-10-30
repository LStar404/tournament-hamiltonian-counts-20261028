module

public import TournamentHamiltonian.TripleContraction.Reindex

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The algebraic sentinel has weight one in both directions and on its loop.
It is not a tournament or a random augmentation. -/
def sentinel {α : Type*} (A : Matrix α α ℝ) : Matrix (Option α) (Option α) ℝ
  | some x, some y => A x y
  | _, _ => 1

@[simp] theorem sentinel_none_left {α : Type*} (A : Matrix α α ℝ) (x : Option α) :
    sentinel A none x=1 := by cases x <;> rfl
@[simp] theorem sentinel_none_right {α : Type*} (A : Matrix α α ℝ) (x : Option α) :
    sentinel A x none=1 := by cases x <;> rfl
@[simp] theorem sentinel_some {α : Type*} (A : Matrix α α ℝ) (x y : α) :
    sentinel A (some x) (some y)=A x y := rfl

def finTailEquiv (n : ℕ) : Fin n ≃ Retain (0 : Fin (n+1)) where
  toFun i := ⟨i.succ,Fin.succ_ne_zero i⟩
  invFun x := x.val.pred x.property
  left_inv i := Fin.pred_succ i
  right_inv x := Subtype.ext (Fin.succ_pred x.val x.property)

def rootOrderingEquiv (n : ℕ) :
    Equiv.Perm (Fin n) ≃ {ψ : Equiv.Perm (Fin (n+1)) // ψ 0=0} :=
  (finTailEquiv n).permCongr |>.trans
    ((Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin (n+1) => x≠0)).trans
      (Equiv.subtypeEquivRight (fun ψ => by simp)))

@[simp] theorem rootOrderingEquiv_zero {n : ℕ} (ψ : Equiv.Perm (Fin n)) :
    (rootOrderingEquiv n ψ).val 0=0 := (rootOrderingEquiv n ψ).property
@[simp] theorem rootOrderingEquiv_succ {n : ℕ} (ψ : Equiv.Perm (Fin n)) (i : Fin n) :
    (rootOrderingEquiv n ψ).val i.succ=(ψ i).succ := by
  change Equiv.Perm.ofSubtype ((finTailEquiv n).permCongr ψ) i.succ = _
  rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun x : Fin (n+1) => x≠0)
    (a := i.succ) _ (Fin.succ_ne_zero i)]
  rfl

/-- Fixed-root version of the existing ordering/marked-cycle equivalence.
The inverse is deliberate: the old cycleFromOrdering is backward successor. -/
def rootForwardCycleEquiv (n : ℕ) :
    {ψ : Equiv.Perm (Fin (n+1)) // ψ 0=0} ≃ Full (Fin (n+1)) where
  toFun ψ := ⟨(cycleFromOrdering ψ.val)⁻¹,
    (singleFullCycle_iff_isCycleOn _).mpr (cycleFromOrdering_isCycleOn ψ.val).inv⟩
  invFun σ := ⟨markedCycleOrdering σ.val⁻¹
      ((singleFullCycle_iff_isCycleOn σ.val).mp σ.property).inv 0,
    markedCycleOrdering_zero _ _ _⟩
  left_inv ψ := by
    apply Subtype.ext
    simp only [inv_inv]
    have h := markedCycleOrdering_cycleFromOrdering ψ.val
    simpa only [ψ.property] using h
  right_inv σ := by
    apply Subtype.ext
    change (cycleFromOrdering (markedCycleOrdering σ.val⁻¹
      ((singleFullCycle_iff_isCycleOn σ.val).mp σ.property).inv 0))⁻¹=σ.val
    rw [cycleFromOrdering_markedCycleOrdering,inv_inv]

variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Ordering (α : Type*) [Fintype α] := Fin (Fintype.card α) ≃ α

def extendOrder (π : Ordering α) : Fin (Fintype.card α+1) ≃ Option α :=
  (finSuccEquiv _).trans (Equiv.optionCongr π)

omit [DecidableEq α] in
@[simp] theorem extendOrder_zero (π : Ordering α) : extendOrder π 0=none := by simp [extendOrder]
omit [DecidableEq α] in
@[simp] theorem extendOrder_succ (π : Ordering α) (i : Fin (Fintype.card α)) :
    extendOrder π i.succ=some (π i) := by simp [extendOrder]

/-- Every actual linear ordering corresponds to one complete forward successor
cycle through the unique sentinel. There is no root multiplicity factor. -/
def orderingCycleEquiv : Ordering α ≃ Full (Option α) :=
  let n := Fintype.card α
  let e := (Fintype.equivFin α).symm
  (orderingEquiv e).symm |>.trans ((rootOrderingEquiv n).trans
    ((rootForwardCycleEquiv n).trans (fullCongr ((finSuccEquiv n).trans (Equiv.optionCongr e)))))

theorem orderingCycleEquiv_rotate (π : Ordering α) (i : Fin (Fintype.card α+1)) :
    (orderingCycleEquiv π).val (extendOrder π i)=extendOrder π (finRotate _ i) := by
  let n := Fintype.card α
  let e := (Fintype.equivFin α).symm
  let ψ : Equiv.Perm (Fin n) := π.trans e.symm
  let φ := (rootOrderingEquiv n ψ).val
  let E := (finSuccEquiv n).trans (Equiv.optionCongr e)
  have he (j : Fin (n+1)) : E (φ j)=extendOrder π j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [E,φ]
    · simp [E,φ,ψ]
      rfl
  change E ((cycleFromOrdering φ)⁻¹ (E.symm (extendOrder π i))) = _
  rw [← he i, E.symm_apply_apply, cycleFromOrdering_inv_apply, he]

/-- Its successor permutation is exactly conjugated forward rotation. -/
theorem orderingCycleEquiv_val (π : Ordering α) :
    (orderingCycleEquiv π).val=(extendOrder π).permCongr (finRotate _) := by
  apply Equiv.ext
  intro x
  obtain ⟨i,rfl⟩ := (extendOrder π).surjective x
  rw [orderingCycleEquiv_rotate]
  simp

end
end TripleContraction
