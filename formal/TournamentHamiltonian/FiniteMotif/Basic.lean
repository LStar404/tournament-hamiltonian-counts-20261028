module

public import TournamentHamiltonian.TripleContraction.Uniform
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

set_option autoImplicit false
namespace FiniteMotif
open TripleContraction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Motif (d m : ℕ) := Fin d × (Fin 3 ↪ Fin m)

namespace Motif
variable {d m : ℕ}
def vertex (t : Motif d m) (i : Fin 3) : Fin (d*m) :=
  finProdFinEquiv (t.1,t.2 i)

theorem vertex_injective (t : Motif d m) : Function.Injective t.vertex := by
  intro i j h
  exact t.2.injective (congrArg Prod.snd (finProdFinEquiv.injective h))

def triple (t : Motif d m) : Triple (Fin (d*m)) where
  first := t.vertex 0
  middle := t.vertex 1
  last := t.vertex 2
  first_middle := t.vertex_injective.ne (by decide)
  first_last := t.vertex_injective.ne (by decide)
  middle_last := t.vertex_injective.ne (by decide)

@[simp] theorem block_vertex (t : Motif d m) (i : Fin 3) : block (t.vertex i)=t.1 := by
  simp [vertex,block]

theorem sameBlock (t : Motif d m) : SameBlock t.triple := by
  simp [SameBlock,triple]

theorem ext_vertex {t s : Motif d m} (h : ∀ i, t.vertex i=s.vertex i) : t=s := by
  have hb := congrArg Prod.fst (finProdFinEquiv.injective (h 0))
  have he : t.2=s.2 := by
    apply DFunLike.ext
    intro i
    exact congrArg Prod.snd (finProdFinEquiv.injective (h i))
  exact Prod.ext hb he

theorem triple_injective : Function.Injective (triple : Motif d m → _) := by
  intro t s h
  apply ext_vertex
  intro i
  fin_cases i
  · exact congrArg Triple.first h
  · exact congrArg Triple.middle h
  · exact congrArg Triple.last h

/-- Disjoint vertex sets, not merely different block labels. -/
def Disjoint (t s : Motif d m) : Prop := ∀ i j, t.vertex i≠s.vertex j

theorem disjoint_iff (t s : Motif d m) :
    t.Disjoint s ↔ t.1≠s.1 ∨ _root_.Disjoint (Set.range t.2) (Set.range s.2) := by
  change (∀ i j, t.vertex i≠s.vertex j) ↔ _ ∨ _
  by_cases hb : t.1=s.1
  · simp only [hb,ne_self_iff_false,false_or]
    constructor
    · intro h
      apply Set.disjoint_left.mpr
      intro x ⟨i,hi⟩ ⟨j,hj⟩
      exact h i j (by simp [vertex,hb,hi,hj])
    · intro h i j he
      have hij := congrArg Prod.snd (finProdFinEquiv.injective he)
      exact Set.disjoint_left.mp h ⟨i,rfl⟩ ⟨j,hij.symm⟩
  · constructor
    · intro _; exact Or.inl hb
    · intro _ i j h
      have he : (t.1,t.2 i)=(s.1,s.2 j) := finProdFinEquiv.injective h
      exact hb (Prod.mk.inj he).1

theorem disjoint_iff_separated (t s : Motif d m) :
    t.Disjoint s ↔ t.triple.Separated s.triple := by
  constructor
  · intro h x hx
    rcases hx with rfl|rfl|rfl <;>
      exact ⟨(h _ _).symm,(h _ _).symm,(h _ _).symm⟩
  · intro h i j
    have hj : s.vertex j=s.triple.first ∨ s.vertex j=s.triple.middle ∨
        s.vertex j=s.triple.last := by fin_cases j <;> simp [triple]
    have hh := h _ hj
    fin_cases i
    · exact hh.1.symm
    · exact hh.2.1.symm
    · exact hh.2.2.symm

/-- The embedding associated with the three explicitly named vertices. -/
def tripleEmbedding (t : Triple (Fin (d*m))) : Fin 3 ↪ Fin (d*m) where
  toFun := ![t.first,t.middle,t.last]
  inj' := by
    intro i j h
    have h01 := t.first_middle
    have h02 := t.first_last
    have h12 := t.middle_last
    fin_cases i <;> fin_cases j <;> dsimp at h <;> simp_all

theorem block_tripleEmbedding (t : Triple (Fin (d*m))) (hb : SameBlock t) (i : Fin 3) :
    block (tripleEmbedding t i)=block t.first := by
  fin_cases i
  · rfl
  · exact hb.1.symm
  · exact hb.2.symm

/-- No same-block directed triple is omitted by the Emb3 parametrization. -/
def ofSameBlock (t : Triple (Fin (d*m))) (hb : SameBlock t) : Motif d m :=
  (block t.first,⟨fun i => (finProdFinEquiv.symm (tripleEmbedding t i)).2,by
    intro i j h
    apply (tripleEmbedding t).injective
    apply finProdFinEquiv.symm.injective
    exact Prod.ext ((block_tripleEmbedding t hb i).trans (block_tripleEmbedding t hb j).symm) h⟩)

theorem vertex_ofSameBlock (t : Triple (Fin (d*m))) (hb : SameBlock t) (i : Fin 3) :
    (ofSameBlock t hb).vertex i=tripleEmbedding t i := by
  apply finProdFinEquiv.symm.injective
  simp only [vertex,ofSameBlock,Equiv.symm_apply_apply]
  exact Prod.ext (block_tripleEmbedding t hb i).symm rfl

theorem triple_ext {α : Type*} {t s : Triple α}
    (h0 : t.first=s.first) (h1 : t.middle=s.middle) (h2 : t.last=s.last) : t=s := by
  cases t
  cases s
  cases h0
  cases h1
  cases h2
  rfl

theorem triple_ofSameBlock (t : Triple (Fin (d*m))) (hb : SameBlock t) :
    (ofSameBlock t hb).triple=t := by
  apply triple_ext
  · exact vertex_ofSameBlock t hb 0
  · exact vertex_ofSameBlock t hb 1
  · exact vertex_ofSameBlock t hb 2

/-- True inverse parametrization of all actual same-block ordered triples. -/
def sameBlockEquiv : Motif d m ≃ {t : Triple (Fin (d*m)) // SameBlock t} where
  toFun t := ⟨t.triple,t.sameBlock⟩
  invFun t := ofSameBlock t.val t.property
  left_inv t := triple_injective (triple_ofSameBlock t.triple t.sameBlock)
  right_inv t := Subtype.ext (triple_ofSameBlock t.val t.property)

/-- In particular the diagonal is always counted among overlaps. -/
theorem not_disjoint_self (t : Motif d m) : ¬t.Disjoint t := by
  intro h
  exact h 0 0 rfl

theorem disjoint_symm {t s : Motif d m} (h : t.Disjoint s) : s.Disjoint t := by
  intro i j
  exact (h j i).symm

end Motif

/-- All small-m boundaries are retained by the natural descending factorial. -/
theorem card_motif (d m : ℕ) : Fintype.card (Motif d m)=d*m.descFactorial 3 := by
  simp

end
end FiniteMotif
