module

public import TournamentHamiltonian.WeightedCycle.Core

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α]

abbrev Retain (v : α) := {x : α // x ≠ v}

/-- Insert v immediately after u, using the forward successor convention. -/
def splice (u v : α) (τ : Equiv.Perm (Retain v)) : Equiv.Perm α :=
  Equiv.Perm.ofSubtype τ * Equiv.swap u v

@[simp] theorem splice_at_left {u v : α} (τ : Equiv.Perm (Retain v)) :
    splice u v τ u = v := by
  simp [splice, Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem]

@[simp] theorem splice_at_new {u v : α} (huv : u ≠ v) (τ : Equiv.Perm (Retain v)) :
    splice u v τ v = τ ⟨u,huv⟩ := by
  simp [splice, Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_mem, huv]

theorem splice_at_other {u v x : α} (hxu : x ≠ u) (hxv : x ≠ v)
    (τ : Equiv.Perm (Retain v)) : splice u v τ x = τ ⟨x,hxv⟩ := by
  simp [splice, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxu hxv,
    Equiv.Perm.ofSubtype_apply_of_mem, hxv]

/-- Actual permutations on the retained vertices are in bijection with ambient
permutations containing the prescribed directed successor edge u to v. -/
def spliceEquiv (u v : α) (_huv : u ≠ v) :
    Equiv.Perm (Retain v) ≃ {σ : Equiv.Perm α // σ u = v} where
  toFun τ := ⟨splice u v τ, splice_at_left τ⟩
  invFun σ := (Equiv.Perm.subtypeEquivSubtypePerm (fun x : α => x ≠ v)).symm
    ⟨σ.val * Equiv.swap u v, by
      intro x hx
      have h : x = v := by simpa using hx
      subst x
      simpa [Equiv.Perm.mul_apply] using σ.property⟩
  left_inv τ := by
    apply (Equiv.Perm.subtypeEquivSubtypePerm (fun x : α => x ≠ v)).injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    simp [splice, mul_assoc]
  right_inv σ := by
    apply Subtype.ext
    change Equiv.Perm.ofSubtype _ * Equiv.swap u v = σ.val
    have he := (Equiv.Perm.subtypeEquivSubtypePerm (fun x : α => x ≠ v)).apply_symm_apply
      (⟨σ.val * Equiv.swap u v, by
        intro x hx
        have h : x = v := by simpa using hx
        subst x
        simpa [Equiv.Perm.mul_apply] using σ.property⟩ :
        {f : Equiv.Perm α // ∀ a, ¬a ≠ v → f a = a})
    have h := congrArg Subtype.val he
    change Equiv.Perm.ofSubtype _ = σ.val * Equiv.swap u v at h
    rw [h]
    simp [mul_assoc]

variable [Fintype α]

/-- Inserting a vertex does not create or merge any other permutation orbit.
The singleton retained orbit is included in this purely combinatorial fact. -/
theorem singleFullCycle_splice_iff {u v : α} (huv : u ≠ v)
    (τ : Equiv.Perm (Retain v)) : SingleFullCycle (splice u v τ) ↔ SingleFullCycle τ := by
  let uR : Retain v := ⟨u,huv⟩
  let : Nonempty (Retain v) := ⟨uR⟩
  let : Nonempty α := ⟨u⟩
  let σ := splice u v τ
  constructor
  · intro hσ
    let r : α → Retain v := fun x => if hx : x = v then uR else ⟨x,hx⟩
    let f : α → CoverCycles τ := fun x => coverCycleOf τ (r x)
    have hr (x : Retain v) : r x.val = x := by simp [r, x.property]
    have hru : r u = uR := by simp [r,huv,uR]
    have hrv : r v = uR := by simp [r]
    have hf : ∀ x, f (σ x) = f x := by
      intro x
      by_cases hxu : x = u
      · subst x
        change coverCycleOf τ (r (splice u v τ u)) = coverCycleOf τ (r u)
        rw [splice_at_left,hrv,hru]
      by_cases hxv : x = v
      · subst x
        change coverCycleOf τ (r (splice u v τ v)) = coverCycleOf τ (r v)
        rw [splice_at_new huv, hr, hrv]
        exact coverCycleOf_apply τ uR
      · change coverCycleOf τ (r (splice u v τ x)) = coverCycleOf τ (r x)
        rw [splice_at_other hxu hxv, hr]
        rw [coverCycleOf_apply]
        congr 1
        simp [r,hxv]
    have hc := (singleFullCycle_iff_isCycleOn σ).mp hσ
    apply Fintype.card_eq_one_of_forall_eq (i := coverCycleOf τ uR)
    intro k
    obtain ⟨x,rfl⟩ := coverCycleOf_surjective τ k
    have he := invariant_color_sameCycle σ f hf (hc.2 (Set.mem_univ x.val) (Set.mem_univ u))
    change coverCycleOf τ (r x.val) = coverCycleOf τ (r u) at he
    simpa only [hr,hru] using he
  · intro hτ
    have hf : ∀ x : Retain v,
        coverCycleOf σ (τ x).val = coverCycleOf σ x.val := by
      intro x
      by_cases hx : x.val = u
      · have he : x = uR := Subtype.ext hx
        subst x
        have h1 := coverCycleOf_apply σ v
        have h2 := coverCycleOf_apply σ u
        dsimp [σ] at h1 h2 ⊢
        rw [splice_at_new huv] at h1
        rw [splice_at_left] at h2
        exact h1.trans h2
      · have h := coverCycleOf_apply σ x.val
        change coverCycleOf σ (splice u v τ x.val) = coverCycleOf σ x.val at h
        rw [splice_at_other hx x.property] at h
        exact h
    have hc := (singleFullCycle_iff_isCycleOn τ).mp hτ
    have he (x : Retain v) : coverCycleOf σ x.val = coverCycleOf σ u :=
      invariant_color_sameCycle τ (fun y => coverCycleOf σ y.val) hf
        (hc.2 (Set.mem_univ x) (Set.mem_univ uR))
    apply Fintype.card_eq_one_of_forall_eq (i := coverCycleOf σ u)
    intro k
    obtain ⟨x,rfl⟩ := coverCycleOf_surjective σ k
    by_cases hx : x = v
    · subst x
      have h := coverCycleOf_apply σ u
      change coverCycleOf σ (splice u v τ u) = coverCycleOf σ u at h
      simpa only [splice_at_left] using h
    · exact he ⟨x,hx⟩

/-- Both directions of the genuine one-orbit splice, not just an injection. -/
def cycleSpliceEquiv (u v : α) (huv : u ≠ v) :
    {τ : Equiv.Perm (Retain v) // SingleFullCycle τ} ≃
      {σ : Equiv.Perm α // SingleFullCycle σ ∧ σ u=v} where
  toFun τ := ⟨splice u v τ.val, (singleFullCycle_splice_iff huv τ.val).mpr τ.property,
    splice_at_left τ.val⟩
  invFun σ := ⟨(spliceEquiv u v huv).symm ⟨σ.val,σ.property.2⟩, by
    apply (singleFullCycle_splice_iff huv _).mp
    have he := (spliceEquiv u v huv).apply_symm_apply ⟨σ.val,σ.property.2⟩
    have h := congrArg Subtype.val he
    change splice u v _ = σ.val at h
    rw [h]
    exact σ.property.1⟩
  left_inv τ := by
    apply Subtype.ext
    exact (spliceEquiv u v huv).symm_apply_apply τ.val
  right_inv σ := by
    apply Subtype.ext
    change splice u v ((spliceEquiv u v huv).symm ⟨σ.val,σ.property.2⟩) = σ.val
    exact congrArg Subtype.val ((spliceEquiv u v huv).apply_symm_apply ⟨σ.val,σ.property.2⟩)

end
end TripleContraction
