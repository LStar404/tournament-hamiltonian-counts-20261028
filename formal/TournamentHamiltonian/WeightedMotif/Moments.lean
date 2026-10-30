module

public import TournamentHamiltonian.WeightedMotif.Events

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace WeightedMotif
open TournamentHamiltonian TripleContraction UniformDeletion FiniteMotif
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

/-- Actual raw normalized first moments. -/
def cycleMean (T : Tournament d) : ℝ := expect (cycleWeight (m:=m) T) (fun σ => (cycleA σ : ℝ)/m)
def pathMean (T : Tournament d) : ℝ := expect (pathWeight (m:=m) T) (fun π => (pathA π : ℝ)/m)
def cycleDisjoint (T : Tournament d) : ℝ := expect (cycleWeight (m:=m) T) (fun σ => (cycleB σ : ℝ)/m^2)
def pathDisjoint (T : Tournament d) : ℝ := expect (pathWeight (m:=m) T) (fun π => (pathB π : ℝ)/m^2)
def cycleOverlap (T : Tournament d) : ℝ := expect (cycleWeight (m:=m) T) (fun σ => (cycleO σ : ℝ)/m^2)
def pathOverlap (T : Tournament d) : ℝ := expect (pathWeight (m:=m) T) (fun π => (pathO π : ℝ)/m^2)
def cycleSecond (T : Tournament d) : ℝ := expect (cycleWeight (m:=m) T) (fun σ => ((cycleA σ : ℝ)/m)^2)
def pathSecond (T : Tournament d) : ℝ := expect (pathWeight (m:=m) T) (fun π => ((pathA π : ℝ)/m)^2)

theorem cycle_first_identity (T : Tournament d) :
    expect (cycleWeight (m:=m) T) (fun σ => (cycleA σ : ℝ))=∑ t : Motif d m,cycleSingle T t := by
  simp only [cycleA_eq_card]
  exact expect_count _ _

theorem path_first_identity (T : Tournament d) :
    expect (pathWeight (m:=m) T) (fun π => (pathA π : ℝ))=∑ t : Motif d m,pathSingle T t := by
  simp only [pathA_eq_card]
  exact expect_count _ _

theorem filtered_subtype_card {α : Type*} [Fintype α] (D Q : α → Prop)
    [Fintype {x // D x}] :
    (Finset.univ.filter (fun x => Q x ∧ D x)).card=
      (Finset.univ.filter (fun x : {x // D x} => Q x.val)).card := by
  have h := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter D Q)
  simpa only [Fintype.card_subtype,and_comm] using h.symm

theorem cycle_disjoint_identity (T : Tournament d) :
    expect (cycleWeight (m:=m) T) (fun σ => (cycleB σ : ℝ))=
      ∑ p : DisjointPair d m,cycleDouble T p := by
  have he (σ : Full (Fin (d*m))) : cycleB σ=
      (Finset.univ.filter (fun p : DisjointPair d m => CycleOccurs σ p.val.1 ∧ CycleOccurs σ p.val.2)).card := by
    rw [cycleB_eq_card]
    refine Finset.card_bij (fun p hp => (⟨p,(Finset.mem_filter.mp hp).2.2.2⟩ : DisjointPair d m)) ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.1⟩
    · intro p hp q hq h
      exact congrArg Subtype.val h
    · intro p hp
      refine ⟨p.val,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2,p.property⟩
  calc
    expect (cycleWeight (m:=m) T) (fun σ => (cycleB σ : ℝ)) =
      expect (cycleWeight (m:=m) T) (fun σ => ((Finset.univ.filter
        (fun p : DisjointPair d m => CycleOccurs σ p.val.1 ∧ CycleOccurs σ p.val.2)).card : ℝ)) := by
      congr 1
      funext σ
      rw [he σ]
    _ = _ := expect_count (ι:=DisjointPair d m) (cycleWeight (m:=m) T)
      (fun p σ => CycleOccurs σ p.val.1 ∧ CycleOccurs σ p.val.2)

theorem path_disjoint_identity (T : Tournament d) :
    expect (pathWeight (m:=m) T) (fun π => (pathB π : ℝ))=
      ∑ p : DisjointPair d m,pathDouble T p := by
  have he (π : Ordering (Fin (d*m))) : pathB π=
      (Finset.univ.filter (fun p : DisjointPair d m => PathOccurs π p.val.1 ∧ PathOccurs π p.val.2)).card := by
    rw [pathB_eq_card]
    refine Finset.card_bij (fun p hp => (⟨p,(Finset.mem_filter.mp hp).2.2.2⟩ : DisjointPair d m)) ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.1⟩
    · intro p hp q hq h
      exact congrArg Subtype.val h
    · intro p hp
      refine ⟨p.val,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2,p.property⟩
  calc
    expect (pathWeight (m:=m) T) (fun π => (pathB π : ℝ)) =
      expect (pathWeight (m:=m) T) (fun π => ((Finset.univ.filter
        (fun p : DisjointPair d m => PathOccurs π p.val.1 ∧ PathOccurs π p.val.2)).card : ℝ)) := by
      congr 1
      funext π
      rw [he π]
    _ = _ := expect_count (ι:=DisjointPair d m) (pathWeight (m:=m) T)
      (fun p π => PathOccurs π p.val.1 ∧ PathOccurs π p.val.2)

theorem cycle_mean_eq (T : Tournament d) : cycleMean (m:=m) T=(∑ t : Motif d m,cycleSingle T t)/m := by
  rw [cycleMean,expect_div,cycle_first_identity]
theorem path_mean_eq (T : Tournament d) : pathMean (m:=m) T=(∑ t : Motif d m,pathSingle T t)/m := by
  rw [pathMean,expect_div,path_first_identity]
theorem cycle_disjoint_eq (T : Tournament d) : cycleDisjoint (m:=m) T=(∑ p : DisjointPair d m,cycleDouble T p)/m^2 := by
  rw [cycleDisjoint,expect_div,cycle_disjoint_identity]
theorem path_disjoint_eq (T : Tournament d) : pathDisjoint (m:=m) T=(∑ p : DisjointPair d m,pathDouble T p)/m^2 := by
  rw [pathDisjoint,expect_div,path_disjoint_identity]

theorem cycle_second_partition (T : Tournament d) :
    cycleSecond (m:=m) T=cycleDisjoint (m:=m) T+cycleOverlap (m:=m) T := by
  have h (σ : Full (Fin (d*m))) : ((cycleA σ : ℝ)/m)^2=(cycleB σ : ℝ)/m^2+(cycleO σ : ℝ)/m^2 := by
    rw [div_pow,←Nat.cast_pow,cycle_partition,Nat.cast_add,add_div]
  simp only [cycleSecond,cycleDisjoint,cycleOverlap,h,expect_add]

theorem path_second_partition (T : Tournament d) :
    pathSecond (m:=m) T=pathDisjoint (m:=m) T+pathOverlap (m:=m) T := by
  have h (π : Ordering (Fin (d*m))) : ((pathA π : ℝ)/m)^2=(pathB π : ℝ)/m^2+(pathO π : ℝ)/m^2 := by
    rw [div_pow,←Nat.cast_pow,path_partition,Nat.cast_add,add_div]
  simp only [pathSecond,pathDisjoint,pathOverlap,h,expect_add]

/-- The old vertex bound is N=dm even for the sentinel implementation of paths. -/
theorem overlap_expect_le {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ x,0≤w x) (hZ : 0<total w) (o : α → ℕ) (ho : ∀ x,o x≤5*(d*m)) (hm : 0<m) :
    0≤expect w (fun x => (o x : ℝ)/(m : ℝ)^2) ∧
      expect w (fun x => (o x : ℝ)/(m : ℝ)^2)≤5*(d : ℝ)/m := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  constructor
  · exact expect_nonneg hw hZ (fun x => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · calc expect w (fun x => (o x : ℝ)/(m : ℝ)^2)
        ≤ expect w (fun _ => (5*(d*m) : ℕ)/(m : ℝ)^2) :=
          expect_mono hw hZ (fun x => div_le_div_of_nonneg_right (by exact_mod_cast ho x) (sq_nonneg _))
      _ = 5*(d : ℝ)/m := by rw [expect_const w hZ]; push_cast; field_simp

theorem cycle_overlap_bounds (T : Tournament d) (hZ : 0<total (cycleWeight (m:=m) T)) (hm : 0<m) :
    0≤cycleOverlap (m:=m) T ∧ cycleOverlap (m:=m) T≤5*(d : ℝ)/m :=
  overlap_expect_le _ (cycleWeight_nonneg T) hZ cycleO
    (fun σ => (cycle_bounds σ).2.2.1.trans (cycle_bounds σ).2.2.2) hm

theorem path_overlap_bounds (T : Tournament d) (hZ : 0<total (pathWeight (m:=m) T)) (hm : 0<m) :
    0≤pathOverlap (m:=m) T ∧ pathOverlap (m:=m) T≤5*(d : ℝ)/m :=
  overlap_expect_le _ (pathWeight_nonneg T) hZ pathO
    (fun π => (path_bounds π).2.2.1.trans (path_bounds π).2.2.2) hm

end
end WeightedMotif
