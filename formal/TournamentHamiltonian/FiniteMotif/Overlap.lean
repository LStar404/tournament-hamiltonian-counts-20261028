module

public import TournamentHamiltonian.FiniteMotif.Occurrences

@[expose] public section

set_option autoImplicit false
namespace FiniteMotif
open TripleContraction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ} {β : Type*} [DecidableEq β]

/-- Five possible starts relative to one occurring triple; values may coincide. -/
def five (σ : Equiv.Perm β) (a : β) : Finset β :=
  {a,σ a,σ (σ a),σ.symm a,σ.symm (σ.symm a)}

theorem card_five_le (σ : Equiv.Perm β) (a : β) : (five σ a).card≤5 := by
  unfold five
  have h1 := Finset.card_insert_le a {σ a,σ (σ a),σ.symm a,σ.symm (σ.symm a)}
  have h2 := Finset.card_insert_le (σ a) {σ (σ a),σ.symm a,σ.symm (σ.symm a)}
  have h3 := Finset.card_insert_le (σ (σ a)) {σ.symm a,σ.symm (σ.symm a)}
  have h4 := Finset.card_insert_le (σ.symm a) {σ.symm (σ.symm a)}
  simp only [Finset.card_singleton] at h4
  omega

theorem five_of_shared (σ : Equiv.Perm β) (a b : β) (i j : Fin 3)
    (h : ![a,σ a,σ (σ a)] i=![b,σ b,σ (σ b)] j) : b∈five σ a := by
  simp only [five,Finset.mem_insert,Finset.mem_singleton]
  fin_cases i <;> fin_cases j <;> dsimp at h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h,σ.symm_apply_apply]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [h,σ.symm_apply_apply,σ.symm_apply_apply]))))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl (σ.injective h).symm
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [σ.injective h,σ.symm_apply_apply]))))
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl (σ.injective h).symm)
  · exact Or.inl (σ.injective (σ.injective h)).symm

omit [DecidableEq β] in
theorem occurs_vertex (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) (t : Motif d m)
    (ht : Occurs e σ t) (i : Fin 3) :
    e (t.vertex i)=![e (t.vertex 0),σ (e (t.vertex 0)),σ (σ (e (t.vertex 0)))] i := by
  fin_cases i
  · rfl
  · exact ht.1.symm
  · exact ht.2.symm.trans (congrArg σ ht.1.symm)

/-- Sharing any of the nine pairs of vertices yields only five possible starts. -/
theorem overlap_start_mem (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β)
    (t s : Motif d m) (ht : Occurs e σ t) (hs : Occurs e σ s)
    (h : ¬t.Disjoint s) : e (s.vertex 0)∈five σ (e (t.vertex 0)) := by
  unfold Motif.Disjoint at h
  push Not at h
  rcases h with ⟨i,j,h⟩
  have he := congrArg e h
  rw [occurs_vertex e σ t ht i,occurs_vertex e σ s hs j] at he
  exact five_of_shared σ _ _ i j he

theorem overlapping_fiber_le (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β)
    (t : Motif d m) (ht : t∈present e σ) :
    ((present e σ).filter (fun s => ¬t.Disjoint s)).card≤5 := by
  let S := (present e σ).filter (fun s => ¬t.Disjoint s)
  have hi : Set.InjOn (fun s : Motif d m => e (s.vertex 0)) S := by
    intro s hs r hr h
    exact first_injective e σ (Finset.mem_filter.mp hs).1
      (Finset.mem_filter.mp hr).1 (e.injective h)
  have hsub : S.image (fun s => e (s.vertex 0)) ⊆ five σ (e (t.vertex 0)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨s,hs,rfl⟩
    exact overlap_start_mem e σ t s (mem_present _ _ _ |>.mp ht)
      (mem_present _ _ _ |>.mp (Finset.mem_filter.mp hs).1) (Finset.mem_filter.mp hs).2
  calc S.card = (S.image (fun s => e (s.vertex 0))).card :=
      (Finset.card_image_of_injOn hi).symm
    _ ≤ (five σ (e (t.vertex 0))).card := Finset.card_le_card hsub
    _ ≤ 5 := card_five_le σ _

theorem overlap_bounds (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    0≤O e σ ∧ O e σ≤5*A e σ ∧ 5*A e σ≤5*(d*m) := by
  refine ⟨Nat.zero_le _,?_,Nat.mul_le_mul_left 5 (A_le_vertices e σ)⟩
  rw [O_eq_sum]
  calc (∑ t∈present e σ, ((present e σ).filter (fun s => ¬t.Disjoint s)).card)
      ≤ ∑ _t∈present e σ, 5 := Finset.sum_le_sum (fun t ht => overlapping_fiber_le e σ t ht)
    _ = 5*A e σ := by simp [A,Nat.mul_comm]

end
end FiniteMotif
