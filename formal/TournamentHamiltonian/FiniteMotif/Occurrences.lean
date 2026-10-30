module

public import TournamentHamiltonian.FiniteMotif.Counts

@[expose] public section

set_option autoImplicit false
namespace FiniteMotif
open TripleContraction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ} {β : Type*}

/-- The same actual old labels may be embedded into a sentinel cycle. -/
def Occurs (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) (t : Motif d m) : Prop :=
  σ (e (t.vertex 0))=e (t.vertex 1) ∧ σ (e (t.vertex 1))=e (t.vertex 2)

def present (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) : Finset (Motif d m) :=
  Finset.univ.filter (Occurs e σ)

def A (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) : ℕ := (present e σ).card

def separatedPairs (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    Finset (Motif d m × Motif d m) :=
  ((present e σ) ×ˢ (present e σ)).filter (fun p => p.1.Disjoint p.2)

def overlappingPairs (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    Finset (Motif d m × Motif d m) :=
  ((present e σ) ×ˢ (present e σ)).filter (fun p => ¬p.1.Disjoint p.2)

def B (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) : ℕ := (separatedPairs e σ).card
def O (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) : ℕ := (overlappingPairs e σ).card

@[simp] theorem mem_present (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) (t : Motif d m) :
    t∈present e σ ↔ Occurs e σ t := by simp [present]

/-- No two occurring directed triples can have the same first vertex. -/
theorem first_injective (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    Set.InjOn (fun t : Motif d m => t.vertex 0) (present e σ) := by
  intro t ht s hs h
  change t∈present e σ at ht
  change s∈present e σ at hs
  change t.vertex 0=s.vertex 0 at h
  rw [mem_present] at ht hs
  have h1 : t.vertex 1=s.vertex 1 :=
    e.injective (ht.1.symm.trans ((congrArg (σ ∘ e) h).trans hs.1))
  have h2 : t.vertex 2=s.vertex 2 :=
    e.injective (ht.2.symm.trans ((congrArg (σ ∘ e) h1).trans hs.2))
  apply Motif.ext_vertex
  intro i
  fin_cases i
  · exact h
  · exact h1
  · exact h2

theorem A_le_vertices (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) : A e σ≤d*m := by
  calc A e σ = ((present e σ).image (fun t => t.vertex 0)).card :=
      (Finset.card_image_of_injOn (first_injective e σ)).symm
    _ ≤ Fintype.card (Fin (d*m)) := Finset.card_le_univ _
    _ = d*m := Fintype.card_fin _

theorem A_eq_zero_of_small_block (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β)
    (hm : m<3) : A e σ=0 := by
  have hcard : Fintype.card (Motif d m)=0 := by
    rw [card_motif,Nat.descFactorial_of_lt hm,Nat.mul_zero]
  have hle := Finset.card_le_univ (present e σ)
  change A e σ≤_ at hle
  omega

/-- The diagonal belongs to O, not B. No independence is involved. -/
theorem square_partition (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    (A e σ)^2=B e σ+O e σ := by
  unfold B O separatedPairs overlappingPairs
  rw [Finset.card_filter_add_card_filter_not,Finset.card_product]
  exact pow_two _

theorem O_eq_sum (e : Fin (d*m) ↪ β) (σ : Equiv.Perm β) :
    O e σ=∑ t∈present e σ, ((present e σ).filter (fun s => ¬t.Disjoint s)).card := by
  simp only [O,overlappingPairs,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.sum_product]

end
end FiniteMotif
