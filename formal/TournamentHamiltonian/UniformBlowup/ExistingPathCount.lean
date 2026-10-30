module

public import TournamentHamiltonian.UniformBlowup.Expectation

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every real vertex ordering is uniquely a permutation followed by a fixed labelling. -/
def arrangementEquiv {d m : ℕ} (e : Arrangement d m) :
    Equiv.Perm (Fin (d*m)) ≃ Arrangement d m where
  toFun σ := σ.trans e
  invFun π := π.trans e.symm
  left_inv σ := by apply Equiv.ext; intro i; exact e.symm_apply_apply (σ i)
  right_inv π := by apply Equiv.ext; intro i; exact e.apply_symm_apply (π i)

def legalArrangementEquiv {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    {σ : Equiv.Perm (Fin (d*m)) // IsHamiltonian (blowup T ω e) σ} ≃
      {π : Arrangement d m // IsPath T ω π} where
  toFun σ := ⟨arrangementEquiv e σ.val, (isPath_iff_existing T ω e σ.val).mpr σ.property⟩
  invFun π := ⟨(arrangementEquiv e).symm π.val, by
    apply (isPath_iff_existing T ω e _).mp
    change IsPath T ω ((arrangementEquiv e) ((arrangementEquiv e).symm π.val))
    simpa using π.property⟩
  left_inv σ := by apply Subtype.ext; exact (arrangementEquiv e).left_inv σ.val
  right_inv π := by apply Subtype.ext; exact (arrangementEquiv e).right_inv π.val

/-- The finite average really averages the manuscript's existing graph path count. -/
theorem pathCount_eq_existing {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    pathCount T ω = TournamentHamiltonian.pathCount (blowup T ω e) := by
  classical
  have h := Fintype.card_congr (legalArrangementEquiv T ω e)
  simpa only [Fintype.card_subtype, pathCount, TournamentHamiltonian.pathCount] using h.symm

theorem existing_path_expectation {d m : ℕ} (T : Tournament d) (e : Arrangement d m) :
    (∑ ω : Sample d m, (TournamentHamiltonian.pathCount (blowup T ω e) : ℝ)) /
      Fintype.card (Sample d m) = weightedPathSum (m := m) T := by
  simp_rw [← pathCount_eq_existing T _ e]
  exact avgPath_eq_weightedPathSum T

end
end UniformBlowup
