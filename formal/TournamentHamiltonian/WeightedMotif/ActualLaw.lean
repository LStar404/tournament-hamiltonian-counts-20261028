module

public import TournamentHamiltonian.WeightedMotif.Law

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open TournamentHamiltonian TripleContraction UniformDeletion Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def cycleWeight (T : Tournament d) (σ : Full (Fin (d*m))) : ℝ := monomial (weightFin (m:=m) T) σ.val
def pathWeight (T : Tournament d) (π : Ordering (Fin (d*m))) : ℝ := pathMonomial (weightFin (m:=m) T) π

theorem weightFin_nonneg (T : Tournament d) (u v : Fin (d*m)) : 0≤weightFin (m:=m) T u v := by
  change 0≤UniformBlowup.weight T (finProdFinEquiv.symm u) (finProdFinEquiv.symm v)
  unfold UniformBlowup.weight
  split_ifs <;> norm_num

theorem cycleWeight_nonneg (T : Tournament d) (σ : Full (Fin (d*m))) : 0≤cycleWeight T σ := by
  unfold cycleWeight monomial
  exact Finset.prod_nonneg (fun _ _ => weightFin_nonneg T _ _)

theorem pathWeight_nonneg (T : Tournament d) (π : Ordering (Fin (d*m))) : 0≤pathWeight T π :=
  Finset.prod_nonneg (fun _ _ => weightFin_nonneg T _ _)

theorem cycle_total (T : Tournament d) : total (cycleWeight (m:=m) T)=WeightedCycle.cyc (weightFin (m:=m) T) :=
  (cyc_eq_sum _).symm

theorem path_total (T : Tournament d) : total (pathWeight (m:=m) T)=WeightedCycle.path (weightFin (m:=m) T) := rfl

theorem cycle_law (T : Tournament d) (hC : 0<WeightedCycle.cyc (weightFin (m:=m) T)) :
    (∀ σ,0≤mass (cycleWeight (m:=m) T) σ) ∧ (∑ σ,mass (cycleWeight (m:=m) T) σ)=1 :=
  normalized_law (cycleWeight_nonneg T) ((cycle_total T).symm ▸ hC)

theorem path_law (T : Tournament d) (hH : 0<WeightedCycle.path (weightFin (m:=m) T)) :
    (∀ π,0≤mass (pathWeight (m:=m) T) π) ∧ (∑ π,mass (pathWeight (m:=m) T) π)=1 :=
  normalized_law (pathWeight_nonneg T) ((path_total T).symm ▸ hH)

theorem cycle_event_eq (T : Tournament d) (P : Equiv.Perm (Fin (d*m)) → Prop) :
    event (cycleWeight T) (fun σ => P σ.val)=
      cycleEvent (weightFin (m:=m) T) P/WeightedCycle.cyc (weightFin (m:=m) T) := by
  rw [event_eq,cycle_total]
  rfl

theorem path_event_eq (T : Tournament d) (P : Ordering (Fin (d*m)) → Prop) :
    event (pathWeight T) P=pathEvent (weightFin (m:=m) T) P/WeightedCycle.path (weightFin (m:=m) T) := by
  rw [event_eq,path_total]
  rfl

/-- Actual Hamilton partition functions are eventually positive; not merely permanents. -/
theorem actual_positive {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T)
    (hd : 0<d) : ∀ᶠ m : ℕ in atTop,
      0<total (cycleWeight (m:=m) T) ∧ 0<total (pathWeight (m:=m) T) := by
  filter_upwards [actual_weight_deletion_ratios T hT hd 0 1 (by norm_num)] with m h
  simpa only [cycle_total,path_total] using And.intro h.1 h.2.1

/-- Separate genuine finite laws at each sufficiently large m. No common probability space. -/
theorem actual_laws {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T)
    (hd : 0<d) : ∀ᶠ m : ℕ in atTop,
      ((∀ σ,0≤mass (cycleWeight (m:=m) T) σ) ∧ (∑ σ,mass (cycleWeight (m:=m) T) σ)=1) ∧
      ((∀ π,0≤mass (pathWeight (m:=m) T) π) ∧ (∑ π,mass (pathWeight (m:=m) T) π)=1) := by
  filter_upwards [actual_positive T hT hd] with m h
  exact ⟨normalized_law (cycleWeight_nonneg T) h.1,normalized_law (pathWeight_nonneg T) h.2⟩

end
end WeightedMotif
