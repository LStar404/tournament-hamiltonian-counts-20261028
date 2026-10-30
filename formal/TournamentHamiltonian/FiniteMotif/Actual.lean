module

public import TournamentHamiltonian.FiniteMotif.Overlap

@[expose] public section

set_option autoImplicit false
namespace FiniteMotif
open TripleContraction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def CycleOccurs (σ : Full (Fin (d*m))) (t : Motif d m) : Prop := t.triple.Holds σ.val
def PathOccurs (π : Ordering (Fin (d*m))) (t : Motif d m) : Prop := t.triple.PathHolds π

theorem cycle_occurs_iff (σ : Full (Fin (d*m))) (t : Motif d m) :
    Occurs (Function.Embedding.refl _) σ.val t ↔ CycleOccurs σ t := Iff.rfl

theorem path_occurs_iff (π : Ordering (Fin (d*m))) (t : Motif d m) :
    Occurs Function.Embedding.some (orderingCycleEquiv π).val t ↔ PathOccurs π t :=
  (t.triple.pathHolds_iff π).symm

/-- Actual Hamilton cycle motif count, with a fixed successor permutation. -/
def cycleA (σ : Full (Fin (d*m))) : ℕ := A (Function.Embedding.refl _) σ.val
def cycleB (σ : Full (Fin (d*m))) : ℕ := B (Function.Embedding.refl _) σ.val
def cycleO (σ : Full (Fin (d*m))) : ℕ := O (Function.Embedding.refl _) σ.val

/-- Actual path motif count: both arcs are genuine consecutive ordering steps. -/
def pathA (π : Ordering (Fin (d*m))) : ℕ := A Function.Embedding.some (orderingCycleEquiv π).val
def pathB (π : Ordering (Fin (d*m))) : ℕ := B Function.Embedding.some (orderingCycleEquiv π).val
def pathO (π : Ordering (Fin (d*m))) : ℕ := O Function.Embedding.some (orderingCycleEquiv π).val

theorem cycleA_eq_card (σ : Full (Fin (d*m))) :
    cycleA σ=(Finset.univ.filter (CycleOccurs σ)).card := rfl

theorem pathA_eq_card (π : Ordering (Fin (d*m))) :
    pathA π=(Finset.univ.filter (PathOccurs π)).card := by
  simp only [pathA,A,present,path_occurs_iff]

theorem cycleB_eq_card (σ : Full (Fin (d*m))) :
    cycleB σ=(Finset.univ.filter (fun p : Motif d m × Motif d m =>
      CycleOccurs σ p.1 ∧ CycleOccurs σ p.2 ∧ p.1.Disjoint p.2)).card := by
  unfold cycleB B separatedPairs present
  congr 1
  ext p
  simp [cycle_occurs_iff,and_assoc]

theorem cycleO_eq_card (σ : Full (Fin (d*m))) :
    cycleO σ=(Finset.univ.filter (fun p : Motif d m × Motif d m =>
      CycleOccurs σ p.1 ∧ CycleOccurs σ p.2 ∧ ¬p.1.Disjoint p.2)).card := by
  unfold cycleO O overlappingPairs present
  congr 1
  ext p
  simp [cycle_occurs_iff,and_assoc]

theorem pathB_eq_card (π : Ordering (Fin (d*m))) :
    pathB π=(Finset.univ.filter (fun p : Motif d m × Motif d m =>
      PathOccurs π p.1 ∧ PathOccurs π p.2 ∧ p.1.Disjoint p.2)).card := by
  unfold pathB B separatedPairs present
  congr 1
  ext p
  simp [path_occurs_iff,and_assoc]

theorem pathO_eq_card (π : Ordering (Fin (d*m))) :
    pathO π=(Finset.univ.filter (fun p : Motif d m × Motif d m =>
      PathOccurs π p.1 ∧ PathOccurs π p.2 ∧ ¬p.1.Disjoint p.2)).card := by
  unfold pathO O overlappingPairs present
  congr 1
  ext p
  simp [path_occurs_iff,and_assoc]

theorem cycle_partition (σ : Full (Fin (d*m))) : (cycleA σ)^2=cycleB σ+cycleO σ :=
  square_partition _ _
theorem path_partition (π : Ordering (Fin (d*m))) : (pathA π)^2=pathB π+pathO π :=
  square_partition _ _

theorem cycle_bounds (σ : Full (Fin (d*m))) :
    cycleA σ≤d*m ∧ 0≤cycleO σ ∧ cycleO σ≤5*cycleA σ ∧ 5*cycleA σ≤5*(d*m) :=
  ⟨A_le_vertices _ _,overlap_bounds _ _⟩

theorem path_bounds (π : Ordering (Fin (d*m))) :
    pathA π≤d*m ∧ 0≤pathO π ∧ pathO π≤5*pathA π ∧ 5*pathA π≤5*(d*m) :=
  ⟨A_le_vertices _ _,overlap_bounds _ _⟩

end
end FiniteMotif
