module

public import TournamentHamiltonian.WeightedMotif.ActualLaw

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open TournamentHamiltonian TripleContraction UniformDeletion FiniteMotif Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def cycleSingle (T : Tournament d) (t : Motif d m) : ℝ :=
  event (cycleWeight T) (fun σ => CycleOccurs σ t)
def pathSingle (T : Tournament d) (t : Motif d m) : ℝ :=
  event (pathWeight T) (fun π => PathOccurs π t)
def cycleDouble (T : Tournament d) (p : DisjointPair d m) : ℝ :=
  event (cycleWeight T) (fun σ => CycleOccurs σ p.val.1 ∧ CycleOccurs σ p.val.2)
def pathDouble (T : Tournament d) (p : DisjointPair d m) : ℝ :=
  event (pathWeight T) (fun π => PathOccurs π p.val.1 ∧ PathOccurs π p.val.2)

theorem cycleSingle_eq (T : Tournament d) (t : Motif d m) (hN : 4≤d*m) :
    cycleSingle T t=(WeightedCycle.cyc (densePrincipalMinor (weightFin (m:=m) T) t.triple.deleted)/
      WeightedCycle.cyc (weightFin (m:=m) T))/4 := by
  change event (cycleWeight T) (fun σ => t.triple.Holds σ.val)=_
  rw [cycle_event_eq,actual_cycle_triple T t.triple t.sameBlock hN]
  ring

theorem pathSingle_eq (T : Tournament d) (t : Motif d m) (hN : 3≤d*m) :
    pathSingle T t=(WeightedCycle.path (densePrincipalMinor (weightFin (m:=m) T) t.triple.deleted)/
      WeightedCycle.path (weightFin (m:=m) T))/4 := by
  unfold pathSingle PathOccurs
  rw [path_event_eq,actual_path_triple T t.triple t.sameBlock hN]
  ring

theorem cycleDouble_eq (T : Tournament d) (p : DisjointPair d m) (hN : 6≤d*m) :
    cycleDouble T p=(WeightedCycle.cyc (densePrincipalMinor (weightFin (m:=m) T)
      (p.val.1.triple.doubleDeleted p.val.2.triple))/WeightedCycle.cyc (weightFin (m:=m) T))/16 := by
  change event (cycleWeight T) (fun σ => p.val.1.triple.Holds σ.val ∧ p.val.2.triple.Holds σ.val)=_
  rw [cycle_event_eq T (fun σ => p.val.1.triple.Holds σ ∧ p.val.2.triple.Holds σ),actual_cycle_double T _ _
    ((Motif.disjoint_iff_separated _ _).mp p.property) p.val.1.sameBlock p.val.2.sameBlock hN]
  ring

theorem pathDouble_eq (T : Tournament d) (p : DisjointPair d m) (hN : 6≤d*m) :
    pathDouble T p=(WeightedCycle.path (densePrincipalMinor (weightFin (m:=m) T)
      (p.val.1.triple.doubleDeleted p.val.2.triple))/WeightedCycle.path (weightFin (m:=m) T))/16 := by
  unfold pathDouble PathOccurs
  rw [path_event_eq,actual_path_double T _ _
    ((Motif.disjoint_iff_separated _ _).mp p.property) p.val.1.sameBlock p.val.2.sameBlock hN]
  ring

/-- Positive actual laws and all single/double event estimates under one common cutoff.
The quantifier over motifs and ordered pairs is after the cutoff. -/
theorem actual_event_errors {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop,
      0<total (cycleWeight (m:=m) T) ∧ 0<total (pathWeight (m:=m) T) ∧ 6≤d*m ∧
      (∀ t : Motif d m,
        |((d*m : ℕ)-1 : ℝ)^2*cycleSingle T t-1|<ε ∧
        |((d*m : ℕ)-1 : ℝ)^2*pathSingle T t-1|<ε) ∧
      (∀ p : DisjointPair d m,
        |((d*m : ℕ)-1 : ℝ)^4*cycleDouble T p-1|<ε ∧
        |((d*m : ℕ)-1 : ℝ)^4*pathDouble T p-1|<ε) := by
  filter_upwards [actual_positive T hT hd,actual_weight_two_four_factors T hT hd ε hε,
    UniformBlockMatrix.eventually_order_ge d 6 hd] with m hpos h hm
  refine ⟨hpos.1,hpos.2,hm,?_,?_⟩
  · intro t
    rw [cycleSingle_eq T t (by omega),pathSingle_eq T t (by omega)]
    exact h.1 _ t.triple.deleted_card
  · intro p
    rw [cycleDouble_eq T p hm,pathDouble_eq T p hm]
    exact h.2 _ (p.val.1.triple.doubleDeleted_card p.val.2.triple
      ((Motif.disjoint_iff_separated _ _).mp p.property))

end
end WeightedMotif
