module

public import TournamentHamiltonian.TripleContraction.Reindex

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle FixedDeletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace Triple
variable (t s : Triple α)

/-- Six distinct labels; no requirement that the two blocks differ. -/
def Separated : Prop := ∀ x, x=s.first ∨ x=s.middle ∨ x=s.last →
  x≠t.first ∧ x≠t.middle ∧ x≠t.last

def keep (x : α) (hm : x≠t.middle) (hl : x≠t.last) : t.Kept :=
  ⟨⟨x,hm⟩,fun h => hl (congrArg Subtype.val h)⟩

omit [Fintype α] [DecidableEq α] in
@[simp] theorem keptVal_keep (x : α) (hm : x≠t.middle) (hl : x≠t.last) :
    t.keptVal (t.keep x hm hl)=x := rfl

omit [Fintype α] [DecidableEq α] in
theorem keptVal_injective : Function.Injective t.keptVal := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

def lift (h : t.Separated s) : Triple t.Kept where
  first := t.keep s.first (h _ (Or.inl rfl)).2.1 (h _ (Or.inl rfl)).2.2
  middle := t.keep s.middle (h _ (Or.inr (Or.inl rfl))).2.1 (h _ (Or.inr (Or.inl rfl))).2.2
  last := t.keep s.last (h _ (Or.inr (Or.inr rfl))).2.1 (h _ (Or.inr (Or.inr rfl))).2.2
  first_middle he := s.first_middle (congrArg t.keptVal he)
  first_last he := s.first_last (congrArg t.keptVal he)
  middle_last he := s.middle_last (congrArg t.keptVal he)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem lift_first (h : t.Separated s) : t.keptVal (t.lift s h).first=s.first := rfl
omit [Fintype α] [DecidableEq α] in
@[simp] theorem lift_middle (h : t.Separated s) : t.keptVal (t.lift s h).middle=s.middle := rfl
omit [Fintype α] [DecidableEq α] in
@[simp] theorem lift_last (h : t.Separated s) : t.keptVal (t.lift s h).last=s.last := rfl

omit [Fintype α] in
/-- Other prescribed arcs are preserved even when both triples lie in one block. -/
theorem holds_expand_lift (h : t.Separated s) (τ : Equiv.Perm t.Kept) :
    (t.lift s h).Holds τ ↔ s.Holds (t.expand τ) := by
  unfold Holds
  have h1 := t.expand_other τ (t.lift s h).first (h _ (Or.inl rfl)).1
  have h2 := t.expand_other τ (t.lift s h).middle (h _ (Or.inr (Or.inl rfl))).1
  simp only [lift_first,lift_middle] at h1 h2
  rw [h1,h2]
  change _ ↔ t.keptVal (τ (t.lift s h).first)=t.keptVal (t.lift s h).middle ∧
    t.keptVal (τ (t.lift s h).middle)=t.keptVal (t.lift s h).last
  rw [t.keptVal_injective.eq_iff,t.keptVal_injective.eq_iff]

end Triple

/-- Explicit composition of two actual contraction/expansion equivalences. -/
def doubleCycleEquiv (t s : Triple α) (h : t.Separated s) :
    Full (t.lift s h).Kept ≃ {σ : Full α // t.Holds σ.val ∧ s.Holds σ.val} :=
  let e := tripleCycleEquiv t
  let g : {τ : Full t.Kept // (t.lift s h).Holds τ.val} ≃
      {σ : {σ : Full α // t.Holds σ.val} // s.Holds σ.val.val} :=
    e.subtypeEquiv (fun τ => t.holds_expand_lift s h τ.val)
  (tripleCycleEquiv (t.lift s h)).trans
    (g.trans (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun σ : Full α => t.Holds σ.val) (fun σ : Full α => s.Holds σ.val)))

@[simp] theorem doubleCycleEquiv_val (t s : Triple α) (h : t.Separated s)
    (τ : Full (t.lift s h).Kept) :
    (doubleCycleEquiv t s h τ).val.val = t.expand ((t.lift s h).expand τ.val) := rfl

omit [Fintype α] [DecidableEq α] in
theorem rowTwins_submatrix {β : Type*} (A : Matrix α α ℝ) (f : β → α)
    (hf : Function.Injective f) {u v : β} (h : RowTwins A (f u) (f v)) :
    RowTwins (A.submatrix f f) u v := by
  intro x hx hy
  exact h (f x) (fun he => hx (hf he)) (fun he => hy (hf he))

theorem double_monomial (A : Matrix α α ℝ) (t s : Triple α) (h : t.Separated s)
    (htm : RowTwins A t.first t.middle) (htl : RowTwins A t.first t.last)
    (hsm : RowTwins A s.first s.middle) (hsl : RowTwins A s.first s.last)
    (hn : 2 ≤ Fintype.card (t.lift s h).Kept) (τ : Full (t.lift s h).Kept) :
    monomial A (doubleCycleEquiv t s h τ).val.val =
      (A t.first t.middle*A t.first t.last)*(A s.first s.middle*A s.first s.last)*
        monomial ((t.lift s h).matrix (t.matrix A)) τ.val := by
  let q := t.lift s h
  have htcard : 2 ≤ Fintype.card t.Kept := by
    let : Nontrivial t.Kept := ⟨⟨q.first,q.middle,q.first_middle⟩⟩
    exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hm : RowTwins (t.matrix A) q.first q.middle :=
    rowTwins_submatrix A t.keptVal t.keptVal_injective hsm
  have hl : RowTwins (t.matrix A) q.first q.last :=
    rowTwins_submatrix A t.keptVal t.keptVal_injective hsl
  have h1 := triple_monomial A t htm htl htcard (tripleCycleEquiv q τ).val
  have h2 := triple_monomial (t.matrix A) q hm hl hn τ
  change monomial A (t.expand (q.expand τ.val)) = _
  change monomial A (t.expand (q.expand τ.val)) = _ at h1
  rw [h1,h2]
  exact (mul_assoc _ _ _).symm

/-- Double event identity before flattening nested principal coordinates. -/
theorem cycle_double_nested (A : Matrix α α ℝ) (t s : Triple α) (h : t.Separated s)
    (htm : RowTwins A t.first t.middle) (htl : RowTwins A t.first t.last)
    (hsm : RowTwins A s.first s.middle) (hsl : RowTwins A s.first s.last)
    (hn : 2 ≤ Fintype.card (t.lift s h).Kept) :
    cycleEvent A (fun σ => t.Holds σ ∧ s.Holds σ) =
      (A t.first t.middle*A t.first t.last)*(A s.first s.middle*A s.first s.last)*
        cyc ((t.lift s h).matrix (t.matrix A)) := by
  rw [cycleEvent_eq_subtype]
  calc
    _ = ∑ τ : Full (t.lift s h).Kept, monomial A (doubleCycleEquiv t s h τ).val.val := by
      symm
      convert! Fintype.sum_equiv (doubleCycleEquiv t s h)
        (fun τ => monomial A (doubleCycleEquiv t s h τ).val.val)
        (fun σ => monomial A σ.val.val) (fun _ => rfl) using 1
      apply Finset.sum_congr
      · ext σ; simp
      · intro σ _; rfl
    _ = _ := by
      simp_rw [double_monomial A t s h htm htl hsm hsl hn]
      rw [← Finset.mul_sum, ← cyc_eq_sum]

end
end TripleContraction
