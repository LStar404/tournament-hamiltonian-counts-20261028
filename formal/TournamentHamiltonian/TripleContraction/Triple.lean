module

public import TournamentHamiltonian.TripleContraction.Weight

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

abbrev Full (α : Type*) [Fintype α] [DecidableEq α] :=
  {σ : Equiv.Perm α // SingleFullCycle σ}

structure Triple (α : Type*) where
  first : α
  middle : α
  last : α
  first_middle : first ≠ middle
  first_last : first ≠ last
  middle_last : middle ≠ last

namespace Triple
variable (t : Triple α)
def firstR : Retain t.middle := ⟨t.first,t.first_middle⟩
def lastR : Retain t.middle := ⟨t.last,t.middle_last.symm⟩
abbrev Kept := Retain t.lastR
def firstK : t.Kept := ⟨t.firstR, fun h => t.first_last (congrArg Subtype.val h)⟩
def Holds (σ : Equiv.Perm α) : Prop := σ t.first=t.middle ∧ σ t.middle=t.last

def expand (τ : Equiv.Perm t.Kept) : Equiv.Perm α :=
  splice t.first t.middle (splice t.firstR t.lastR τ)

def matrix (A : Matrix α α ℝ) : Matrix t.Kept t.Kept ℝ :=
  eraseMatrix (eraseMatrix A t.middle) t.lastR

def keptVal (x : t.Kept) : α := x.val.val

@[simp] theorem expand_first (τ : Equiv.Perm t.Kept) : t.expand τ t.first=t.middle :=
  splice_at_left _
@[simp] theorem expand_middle (τ : Equiv.Perm t.Kept) : t.expand τ t.middle=t.last := by
  unfold expand
  rw [splice_at_new t.first_middle]
  change (splice t.firstR t.lastR τ t.firstR).val = t.last
  rw [splice_at_left]
  rfl
@[simp] theorem expand_last (τ : Equiv.Perm t.Kept) :
    t.expand τ t.last = t.keptVal (τ t.firstK) := by
  unfold expand
  rw [splice_at_other t.first_last.symm t.middle_last.symm]
  change (splice t.firstR t.lastR τ t.lastR).val = _
  rw [splice_at_new (fun h => t.first_last (congrArg Subtype.val h))]
  rfl

theorem expand_other (τ : Equiv.Perm t.Kept) (x : t.Kept)
    (hx : t.keptVal x ≠ t.first) : t.expand τ (t.keptVal x) = t.keptVal (τ x) := by
  change x.val.val ≠ t.first at hx
  unfold expand keptVal
  rw [splice_at_other hx x.val.property]
  change (splice t.firstR t.lastR τ x.val).val = _
  rw [splice_at_other (fun h => hx (congrArg Subtype.val h)) x.property]

end Triple

variable [Fintype α]

def fullSpliceEquiv (u v : α) (huv : u ≠ v) :
    Full (Retain v) ≃ {σ : Full α // σ.val u=v} :=
  (cycleSpliceEquiv u v huv).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter SingleFullCycle (fun σ : Equiv.Perm α => σ u=v)).symm

@[simp] theorem fullSpliceEquiv_val (u v : α) (huv : u ≠ v) (τ : Full (Retain v)) :
    (fullSpliceEquiv u v huv τ).val.val = splice u v τ.val := rfl

/-- Actual contraction and expansion for a prescribed directed triple.
The bijection itself includes singleton completions; weighted cycle identities
will separately require at least two retained vertices. -/
def tripleCycleEquiv (t : Triple α) : Full t.Kept ≃ {σ : Full α // t.Holds σ.val} :=
  let e := fullSpliceEquiv t.first t.middle t.first_middle
  let f := fullSpliceEquiv t.firstR t.lastR (fun h => t.first_last (congrArg Subtype.val h))
  let g : {τ : Full (Retain t.middle) // τ.val t.firstR=t.lastR} ≃
      {σ : {σ : Full α // σ.val t.first=t.middle} // σ.val.val t.middle=t.last} :=
    e.subtypeEquiv (by
      intro τ
      change τ.val t.firstR=t.lastR ↔ splice t.first t.middle τ.val t.middle=t.last
      rw [splice_at_new t.first_middle]
      exact Subtype.ext_iff)
  f.trans (g.trans (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun σ : Full α => σ.val t.first=t.middle) (fun σ : Full α => σ.val t.middle=t.last)))

@[simp] theorem tripleCycleEquiv_val (t : Triple α) (τ : Full t.Kept) :
    (tripleCycleEquiv t τ).val.val = t.expand τ.val := rfl

omit [Fintype α] [DecidableEq α] in
theorem triple_inner_rowTwins (A : Matrix α α ℝ) (t : Triple α)
    (h : RowTwins A t.first t.last) : RowTwins (eraseMatrix A t.middle) t.firstR t.lastR := by
  intro x hx hy
  exact h x.val (fun he => hx (Subtype.ext he)) (fun he => hy (Subtype.ext he))

theorem triple_monomial (A : Matrix α α ℝ) (t : Triple α)
    (hmid : RowTwins A t.first t.middle) (hlast : RowTwins A t.first t.last)
    (hn : 2 ≤ Fintype.card t.Kept) (τ : Full t.Kept) :
    monomial A (tripleCycleEquiv t τ).val.val =
      (A t.first t.middle * A t.first t.last) * monomial (t.matrix A) τ.val := by
  have hu : t.firstR ≠ t.lastR := fun h => t.first_last (congrArg Subtype.val h)
  have hne : splice t.firstR t.lastR τ.val t.firstR ≠ t.firstR := by
    rw [splice_at_left]
    exact hu.symm
  change monomial A (splice t.first t.middle (splice t.firstR t.lastR τ.val)) = _
  rw [splice_monomial A t.first_middle hmid _ hne,
    splice_monomial (eraseMatrix A t.middle) hu (triple_inner_rowTwins A t hlast) τ.val
      (cycle_successor_ne hn τ.val τ.property _)]
  exact (mul_assoc _ _ _).symm

end
end TripleContraction
