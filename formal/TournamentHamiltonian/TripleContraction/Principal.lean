module

public import TournamentHamiltonian.TripleContraction.Double

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle FixedDeletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace Triple
variable (t s : Triple α)

def doubleDeleted : Finset α := t.deleted ∪ s.deleted

def doubleVal (h : t.Separated s) (x : (t.lift s h).Kept) : α :=
  t.keptVal ((t.lift s h).keptVal x)

omit [Fintype α] [DecidableEq α] in
theorem keptVal_ne_middle (x : t.Kept) : t.keptVal x≠t.middle := x.val.property
omit [Fintype α] [DecidableEq α] in
theorem keptVal_ne_last (x : t.Kept) : t.keptVal x≠t.last :=
  fun h => x.property (Subtype.ext h)

def doubleKeptEquiv (h : t.Separated s) : (t.lift s h).Kept ≃ ((t.doubleDeleted s)ᶜ : Finset α) where
  toFun x := ⟨t.doubleVal s h x,by
    simp only [doubleDeleted,deleted,Finset.mem_compl,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,not_or]
    refine ⟨⟨t.keptVal_ne_middle _,t.keptVal_ne_last _⟩,?_,?_⟩
    · intro he
      exact (t.lift s h).keptVal_ne_middle x (t.keptVal_injective he)
    · intro he
      exact (t.lift s h).keptVal_ne_last x (t.keptVal_injective he)⟩
  invFun x := by
    have hx : (x.val≠t.middle ∧ x.val≠t.last) ∧ (x.val≠s.middle ∧ x.val≠s.last) := by
      simpa only [doubleDeleted,deleted,Finset.mem_compl,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,not_or] using x.property
    let y := t.keep x.val hx.1.1 hx.1.2
    exact (t.lift s h).keep y
      (fun he => hx.2.1 (congrArg t.keptVal he)) (fun he => hx.2.2 (congrArg t.keptVal he))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype α] in
theorem doubleDeleted_card (h : t.Separated s) : (t.doubleDeleted s).card=4 := by
  have hd : Disjoint t.deleted s.deleted := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hy' : x=s.first ∨ x=s.middle ∨ x=s.last := by
      simpa only [deleted,Finset.mem_insert,Finset.mem_singleton] using Or.inr hy
    have hx' : x=t.middle ∨ x=t.last := by simpa [deleted] using hx
    exact hx'.elim (h x hy').2.1 (h x hy').2.2
  rw [doubleDeleted,Finset.card_union_of_disjoint hd,t.deleted_card,s.deleted_card]

theorem doubleKept_card (h : t.Separated s) :
    Fintype.card (t.lift s h).Kept=Fintype.card α-4 := by
  rw [Fintype.card_congr (t.doubleKeptEquiv s h)]
  simp [t.doubleDeleted_card s h]

theorem doubleMatrix_eq (h : t.Separated s) (A : Matrix α α ℝ) :
    (t.lift s h).matrix (t.matrix A)=
      (principal A (t.doubleDeleted s)).submatrix (t.doubleKeptEquiv s h) (t.doubleKeptEquiv s h) := rfl

theorem cyc_doubleMatrix_eq (h : t.Separated s) (A : Matrix α α ℝ) :
    cyc ((t.lift s h).matrix (t.matrix A))=cyc (principal A (t.doubleDeleted s)) := by
  let : Nonempty (t.lift s h).Kept := ⟨(t.lift s h).firstK⟩
  rw [doubleMatrix_eq]
  exact UniformFinalScalars.cyc_submatrix_equiv (t.doubleKeptEquiv s h) _

end Triple

/-- The principal completion type, rather than a nested substitute, is the
source of this full actual single-triple equivalence. -/
def principalTripleCycleEquiv (t : Triple α) :
    Full (t.deletedᶜ : Finset α) ≃ {σ : Full α // t.Holds σ.val} := by
  let : Nonempty (t.deletedᶜ : Finset α) := ⟨t.keptEquiv t.firstK⟩
  exact (fullCongr t.keptEquiv.symm).trans (tripleCycleEquiv t)

def principalDoubleCycleEquiv (t s : Triple α) (h : t.Separated s) :
    Full ((t.doubleDeleted s)ᶜ : Finset α) ≃
      {σ : Full α // t.Holds σ.val ∧ s.Holds σ.val} := by
  let : Nonempty ((t.doubleDeleted s)ᶜ : Finset α) :=
    ⟨t.doubleKeptEquiv s h (t.lift s h).firstK⟩
  exact (fullCongr (t.doubleKeptEquiv s h).symm).trans (doubleCycleEquiv t s h)

/-- Exact double-triple completion sum on the ambient four-point principal deletion. -/
theorem cycle_double (A : Matrix α α ℝ) (t s : Triple α) (h : t.Separated s)
    (htm : RowTwins A t.first t.middle) (htl : RowTwins A t.first t.last)
    (hsm : RowTwins A s.first s.middle) (hsl : RowTwins A s.first s.last)
    (hn : 2 ≤ Fintype.card (t.lift s h).Kept) :
    cycleEvent A (fun σ => t.Holds σ ∧ s.Holds σ) =
      (A t.first t.middle*A t.first t.last)*(A s.first s.middle*A s.first s.last)*
        cyc (principal A (t.doubleDeleted s)) := by
  rw [cycle_double_nested A t s h htm htl hsm hsl hn,t.cyc_doubleMatrix_eq s h]

end
end TripleContraction
