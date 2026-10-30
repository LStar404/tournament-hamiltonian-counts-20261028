module

public import TournamentHamiltonian.BaseRelabel.Candidates
public import TournamentHamiltonian.NonregularDecay.ExpectationDecay

@[expose] public section

set_option autoImplicit false
namespace BaseRelabel
open TournamentHamiltonian UniformBlowup RegularOrientation NonregularDecay
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact equality of the actual uniform-block path expectations, all block sizes. -/
theorem avgPath_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d)) :
    avgPath (m := m) (relabelTournament T e) = avgPath (m := m) T := by
  unfold avgPath
  congr 1
  exact Fintype.sum_equiv (sampleEquiv e) _ _ (fun ω => by rw [pathCount_relabel])

/-- Exact equality of the actual uniform-block unrooted-cycle expectations. -/
theorem avgCycle_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d)) :
    avgCycle (m := m) (relabelTournament T e) = avgCycle (m := m) T := by
  unfold avgCycle
  congr 1
  exact Fintype.sum_equiv (sampleEquiv e) _ _ (fun ω => by rw [cycleCount_relabel])

/-- Samplewise regular-block path equality, via reindexing whole regular blocks. -/
theorem regular_pathCount_relabel {d k : ℕ} (T : Tournament d)
    (e : Equiv.Perm (Fin d)) (ω : RegularSample d k) :
    UniformBlowup.pathCount (relabelTournament T e) (regularSampleBits ω) =
      UniformBlowup.pathCount T (regularSampleBits (regularSampleEquiv e ω)) := by
  rw [pathCount_relabel, regularSampleBits_equiv]

theorem regular_cycleCount_relabel {d k : ℕ} (T : Tournament d)
    (e : Equiv.Perm (Fin d)) (ω : RegularSample d k) :
    cycleCount (relabelTournament T e) (regularSampleBits ω) =
      cycleCount T (regularSampleBits (regularSampleEquiv e ω)) := by
  rw [cycleCount_relabel, regularSampleBits_equiv]

/-- Exact equality of the existing actual regular-block path expectations, m=2k+1. -/
theorem regularAvgPath_relabel {d : ℕ} (T : Tournament d)
    (e : Equiv.Perm (Fin d)) (k : ℕ) :
    regularAvgPath (relabelTournament T e) k = regularAvgPath T k := by
  unfold regularAvgPath
  congr 1
  exact Fintype.sum_equiv (regularSampleEquiv e) _ _
    (fun ω => by rw [regular_pathCount_relabel])

/-- Exact equality of the existing actual regular-block cycle expectations, m=2k+1. -/
theorem regularAvgCycle_relabel {d : ℕ} (T : Tournament d)
    (e : Equiv.Perm (Fin d)) (k : ℕ) :
    regularAvgCycle (relabelTournament T e) k = regularAvgCycle T k := by
  unfold regularAvgCycle
  congr 1
  exact Fintype.sum_equiv (regularSampleEquiv e) _ _
    (fun ω => by rw [regular_cycleCount_relabel])

/-- Ordinary base isomorphism gives each of the four actual expectation equalities.
No signed-switching or spectral equality premise occurs. -/
theorem four_expectations_eq_of_relabel {d : ℕ} (T U : Tournament d)
    (h : ∃ e : Equiv.Perm (Fin d), relabelTournament T e = U) (m k : ℕ) :
    avgPath (m := m) T = avgPath (m := m) U ∧
    avgCycle (m := m) T = avgCycle (m := m) U ∧
    regularAvgPath T k = regularAvgPath U k ∧
    regularAvgCycle T k = regularAvgCycle U k := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨(avgPath_relabel T e).symm, (avgCycle_relabel T e).symm,
    (regularAvgPath_relabel T e k).symm, (regularAvgCycle_relabel T e k).symm⟩

end
end BaseRelabel
