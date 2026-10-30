module
public import Tournament.Paths
public import TournamentHamiltonian.NonregularNormalization.PathRate
@[expose] public section
set_option autoImplicit false
namespace PaperAugmentationNormalization
open TournamentHamiltonian NonregularDecay

/-- Literal normalized conditional identity, on at least two old vertices. -/
theorem normalized_augmentation {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n+2))) :
    (TournamentPaths.pathCount T : ℝ)/meanPaths (n+2) =
      (TournamentPaths.uniformAugmentedCycleAverage T : ℝ)/meanCycles (n+3) := by
  have h : (TournamentPaths.uniformAugmentedCycleAverage T : ℝ) =
      (TournamentPaths.pathCount T : ℝ)/4 := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      congrArg (fun x : ℚ => (x : ℝ)) (TournamentPaths.augmentation_average T)
  have hm : meanPaths (n+2)=4*meanCycles (n+3) := by
    simpa only [Nat.add_assoc] using
      NonregularNormalization.meanPaths_eq_four_meanCycles_succ (n:=n+2) (by omega)
  have hp : 0<meanCycles (n+3) := meanCycles_pos _
  rw [h,hm]
  field_simp [hp.ne']

/-- The finite-expectation display in Lemma11.5. The identity holds for every
finite weight vector, in particular every actual finite probability law.
No measure, shared infinite sample space, or independence premise is introduced. -/
theorem normalized_finite_augmentation {n : ℕ} {ι : Type*} [Fintype ι]
    (T : ι → TournamentPaths.Tournament (Fin (n+2))) (w : ι → ℝ) :
    (∑ i, w i*(TournamentPaths.pathCount (T i) : ℝ))/meanPaths (n+2) =
      (∑ i, w i*(TournamentPaths.uniformAugmentedCycleAverage (T i) : ℝ))/meanCycles (n+3) := by
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  calc
    w i*(TournamentPaths.pathCount (T i) : ℝ)/meanPaths (n+2) =
      w i*((TournamentPaths.pathCount (T i) : ℝ)/meanPaths (n+2)) := by ring
    _ = w i*((TournamentPaths.uniformAugmentedCycleAverage (T i) : ℝ)/meanCycles (n+3)) := by
      rw [normalized_augmentation]
    _ = _ := by ring

end PaperAugmentationNormalization
