module

public import TournamentHamiltonian.TripleContraction.PathEvents
public import TournamentHamiltonian.UniformDeletion.Homogeneity

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle FixedDeletion UniformDeletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Block label in precisely the frozen Fin reindexing of the actual model. -/
def block {d m : ℕ} (i : Fin (d*m)) : Fin d := (finProdFinEquiv.symm i).1

def SameBlock {d m : ℕ} (t : Triple (Fin (d*m))) : Prop :=
  block t.first=block t.middle ∧ block t.first=block t.last

theorem actual_weight_half {d m : ℕ} (T : Tournament d) (u v : Fin (d*m))
    (huv : u≠v) (hb : block u=block v) : weightFin T u v=(1/2 : ℝ) := by
  have he : finProdFinEquiv.symm u≠finProdFinEquiv.symm v := finProdFinEquiv.symm.injective.ne huv
  change (finProdFinEquiv.symm u).1=(finProdFinEquiv.symm v).1 at hb
  change UniformBlowup.weight T (finProdFinEquiv.symm u) (finProdFinEquiv.symm v)=_
  simp only [UniformBlowup.weight,ite_eq_right he,ite_eq_left hb]

theorem actual_weight_rowTwins {d m : ℕ} (T : Tournament d) (u v : Fin (d*m))
    (hb : block u=block v) : RowTwins (weightFin T) u v := by
  intro x hxu hxv
  have hux : finProdFinEquiv.symm u≠finProdFinEquiv.symm x :=
    finProdFinEquiv.symm.injective.ne hxu.symm
  have hvx : finProdFinEquiv.symm v≠finProdFinEquiv.symm x :=
    finProdFinEquiv.symm.injective.ne hxv.symm
  change (finProdFinEquiv.symm u).1=(finProdFinEquiv.symm v).1 at hb
  change UniformBlowup.weight T (finProdFinEquiv.symm v) (finProdFinEquiv.symm x)=
    UniformBlowup.weight T (finProdFinEquiv.symm u) (finProdFinEquiv.symm x)
  simp only [UniformBlowup.weight,ite_eq_right hux,ite_eq_right hvx,← hb]

/-- Actual uniform W, genuine successor-cycle event, exact principal completion.
No regular base, positivity, or asymptotic hypothesis is imposed. -/
theorem actual_cycle_triple {d m : ℕ} (T : Tournament d) (t : Triple (Fin (d*m)))
    (hb : SameBlock t) (hn : 4 ≤ d*m) :
    cycleEvent (weightFin T) t.Holds=(1/4 : ℝ)*cyc (densePrincipalMinor (weightFin T) t.deleted) := by
  have hk : 2 ≤ Fintype.card t.Kept := by rw [t.kept_card,Fintype.card_fin]; omega
  rw [cycle_triple (weightFin T) t
    (actual_weight_rowTwins T _ _ hb.1) (actual_weight_rowTwins T _ _ hb.2) hk,
    actual_weight_half T _ _ t.first_middle hb.1,actual_weight_half T _ _ t.first_last hb.2]
  norm_num [principal_fin]

/-- Includes the six-vertex boundary and permits the two triples in one block. -/
theorem actual_cycle_double {d m : ℕ} (T : Tournament d)
    (t s : Triple (Fin (d*m))) (h : t.Separated s) (ht : SameBlock t) (hs : SameBlock s)
    (hn : 6 ≤ d*m) :
    cycleEvent (weightFin T) (fun σ => t.Holds σ ∧ s.Holds σ)=
      (1/16 : ℝ)*cyc (densePrincipalMinor (weightFin T) (t.doubleDeleted s)) := by
  have hk : 2 ≤ Fintype.card (t.lift s h).Kept := by
    rw [t.doubleKept_card s h,Fintype.card_fin]; omega
  rw [cycle_double (weightFin T) t s h
    (actual_weight_rowTwins T _ _ ht.1) (actual_weight_rowTwins T _ _ ht.2)
    (actual_weight_rowTwins T _ _ hs.1) (actual_weight_rowTwins T _ _ hs.2) hk,
    actual_weight_half T _ _ t.first_middle ht.1,actual_weight_half T _ _ t.first_last ht.2,
    actual_weight_half T _ _ s.first_middle hs.1,actual_weight_half T _ _ s.first_last hs.2]
  norm_num [principal_fin]

/-- Three ambient vertices are allowed: the retained path is the singleton empty product. -/
theorem actual_path_triple {d m : ℕ} (T : Tournament d) (t : Triple (Fin (d*m)))
    (hb : SameBlock t) (hn : 3 ≤ d*m) :
    pathEvent (weightFin T) t.PathHolds=(1/4 : ℝ)*path (densePrincipalMinor (weightFin T) t.deleted) := by
  rw [path_triple (weightFin T) t
    (actual_weight_rowTwins T _ _ hb.1) (actual_weight_rowTwins T _ _ hb.2)
      (by simpa using hn),
    actual_weight_half T _ _ t.first_middle hb.1,actual_weight_half T _ _ t.first_last hb.2]
  norm_num [principal_fin]

theorem actual_path_double {d m : ℕ} (T : Tournament d)
    (t s : Triple (Fin (d*m))) (h : t.Separated s) (ht : SameBlock t) (hs : SameBlock s)
    (hn : 6 ≤ d*m) :
    pathEvent (weightFin T) (fun π => t.PathHolds π ∧ s.PathHolds π)=
      (1/16 : ℝ)*path (densePrincipalMinor (weightFin T) (t.doubleDeleted s)) := by
  rw [path_double (weightFin T) t s h
    (actual_weight_rowTwins T _ _ ht.1) (actual_weight_rowTwins T _ _ ht.2)
    (actual_weight_rowTwins T _ _ hs.1) (actual_weight_rowTwins T _ _ hs.2)
      (by simpa using hn),
    actual_weight_half T _ _ t.first_middle ht.1,actual_weight_half T _ _ t.first_last ht.2,
    actual_weight_half T _ _ s.first_middle hs.1,actual_weight_half T _ _ s.first_last hs.2]
  norm_num [principal_fin]

end
end TripleContraction
