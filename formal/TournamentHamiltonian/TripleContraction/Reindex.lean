module

public import TournamentHamiltonian.TripleContraction.Triple
public import TournamentHamiltonian.FixedDeletion.Reindex

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle FixedDeletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem isCycleOn_permCongr (e : α ≃ β) (σ : Equiv.Perm α)
    (hσ : σ.IsCycleOn Set.univ) : (e.permCongr σ).IsCycleOn Set.univ := by
  refine ⟨(e.permCongr σ).bijective.bijOn_univ,?_⟩
  intro x _ y _
  obtain ⟨n,hn⟩ := hσ.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨n,?_⟩
  have hp := map_zpow e.permCongrHom σ n
  change e.permCongr (σ^n) = (e.permCongr σ)^n at hp
  rw [← hp]
  change e ((σ^n) (e.symm x)) = y
  rw [hn,e.apply_symm_apply]

def fullCongr [Nonempty α] (e : α ≃ β) : Full α ≃ Full β := by
  let : Nonempty β := ⟨e (Classical.choice ‹Nonempty α›)⟩
  apply e.permCongr.subtypeEquiv
  intro σ
  rw [singleFullCycle_iff_isCycleOn, singleFullCycle_iff_isCycleOn]
  constructor
  · exact isCycleOn_permCongr e σ
  · intro h
    have hh := isCycleOn_permCongr e.symm (e.permCongr σ) h
    change (e.permCongr.symm (e.permCongr σ)).IsCycleOn Set.univ at hh
    simpa only [Equiv.symm_apply_apply] using hh

@[simp] theorem fullCongr_val [Nonempty α] (e : α ≃ β) (σ : Full α) :
    (fullCongr e σ).val = e.permCongr σ.val := rfl

omit [DecidableEq α] [DecidableEq β] in
theorem monomial_congr (e : α ≃ β) (A : Matrix β β ℝ) (σ : Equiv.Perm α) :
    monomial A (e.permCongr σ) = monomial (A.submatrix e e) σ := by
  symm
  apply Fintype.prod_equiv e
  intro x
  simp [Matrix.submatrix_apply]

namespace Triple
variable (t : Triple α)
def deleted : Finset α := {t.middle,t.last}

def keptEquiv : t.Kept ≃ (t.deletedᶜ : Finset α) where
  toFun x := ⟨x.val.val, by
    simp only [deleted,Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨x.val.property, fun h => x.property (Subtype.ext h)⟩⟩
  invFun x := ⟨⟨x.val,by
    have h := Finset.mem_compl.mp x.property
    intro hm
    exact h (by simp [deleted,hm])⟩,by
      intro h
      have he := congrArg Subtype.val h
      change x.val = t.last at he
      exact (Finset.mem_compl.mp x.property) (by simp [deleted,he])⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem keptEquiv_val (x : t.Kept) : (t.keptEquiv x).val=t.keptVal x := rfl

omit [Fintype α] in
theorem deleted_card : t.deleted.card=2 := by simp [deleted,t.middle_last]

theorem kept_card : Fintype.card t.Kept=Fintype.card α-2 := by
  rw [Fintype.card_congr t.keptEquiv]
  simp [deleted_card]

theorem matrix_eq (A : Matrix α α ℝ) :
    t.matrix A = (principal A t.deleted).submatrix t.keptEquiv t.keptEquiv := rfl

theorem cyc_matrix_eq (A : Matrix α α ℝ) : cyc (t.matrix A)=cyc (principal A t.deleted) := by
  let : Nonempty t.Kept := ⟨t.firstK⟩
  rw [matrix_eq]
  exact UniformFinalScalars.cyc_submatrix_equiv t.keptEquiv _

theorem path_matrix_eq (A : Matrix α α ℝ) : path (t.matrix A)=path (principal A t.deleted) := by
  rw [matrix_eq]
  exact UniformFinalScalars.path_submatrix_equiv t.keptEquiv _

end Triple

/-- Actual weighted event sum, before any probability normalization. -/
def cycleEvent (A : Matrix α α ℝ) (P : Equiv.Perm α → Prop) : ℝ :=
  ∑ σ : Full α, if P σ.val then monomial A σ.val else 0

theorem cycleEvent_eq_subtype (A : Matrix α α ℝ) (P : Equiv.Perm α → Prop) :
    cycleEvent A P = ∑ σ : {σ : Full α // P σ.val}, monomial A σ.val.val := by
  unfold cycleEvent
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem cycleEvent_eq_permutation_sum (A : Matrix α α ℝ) (P : Equiv.Perm α → Prop) :
    cycleEvent A P = ∑ σ : Equiv.Perm α,
      if SingleFullCycle σ ∧ P σ then monomial A σ else 0 := by
  unfold cycleEvent
  symm
  simp_rw [ite_and]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Exact single-triple completion sum on the true principal submatrix. -/
theorem cycle_triple (A : Matrix α α ℝ) (t : Triple α)
    (hmid : RowTwins A t.first t.middle) (hlast : RowTwins A t.first t.last)
    (hn : 2 ≤ Fintype.card t.Kept) :
    cycleEvent A t.Holds = (A t.first t.middle*A t.first t.last)*cyc (principal A t.deleted) := by
  rw [cycleEvent_eq_subtype]
  calc
    _ = ∑ τ : Full t.Kept, monomial A (tripleCycleEquiv t τ).val.val := by
      symm
      apply Fintype.sum_equiv (tripleCycleEquiv t)
      intro τ
      rfl
    _ = _ := by
      simp_rw [triple_monomial A t hmid hlast hn]
      rw [← Finset.mul_sum, ← cyc_eq_sum, t.cyc_matrix_eq]

end
end TripleContraction
