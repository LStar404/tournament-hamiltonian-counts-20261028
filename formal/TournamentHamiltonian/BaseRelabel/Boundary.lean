module

public import TournamentHamiltonian.BaseRelabel.Expectations

@[expose] public section

set_option autoImplicit false
namespace BaseRelabel
open TournamentHamiltonian UniformBlowup RegularOrientation NonregularDecay
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Empty base and empty blocks are retained, rather than eliminated by positivity. -/
theorem empty_base_uniform (T : Tournament 0) (e : Equiv.Perm (Fin 0)) (m : ℕ) :
    avgPath (m := m) (relabelTournament T e) = avgPath (m := m) T ∧
    avgCycle (m := m) (relabelTournament T e) = avgCycle (m := m) T :=
  ⟨avgPath_relabel T e, avgCycle_relabel T e⟩

theorem empty_blocks_uniform {d : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d)) :
    avgPath (m := 0) (relabelTournament T e) = avgPath (m := 0) T ∧
    avgCycle (m := 0) (relabelTournament T e) = avgCycle (m := 0) T :=
  ⟨avgPath_relabel T e, avgCycle_relabel T e⟩

theorem empty_base_regular (T : Tournament 0) (e : Equiv.Perm (Fin 0)) (k : ℕ) :
    regularAvgPath (relabelTournament T e) k = regularAvgPath T k ∧
    regularAvgCycle (relabelTournament T e) k = regularAvgCycle T k :=
  ⟨regularAvgPath_relabel T e k, regularAvgCycle_relabel T e k⟩

/-- k=0 is the legitimate one-vertex regular internal block, not m=0. -/
theorem singleton_regular_blocks {d : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d)) :
    regularAvgPath (relabelTournament T e) 0 = regularAvgPath T 0 ∧
    regularAvgCycle (relabelTournament T e) 0 = regularAvgCycle T 0 :=
  ⟨regularAvgPath_relabel T e 0, regularAvgCycle_relabel T e 0⟩

theorem regular_sample_nonempty (d k : ℕ) : 0 < Fintype.card (RegularSample d k) :=
  regularSample_card_pos d k

theorem uniform_sample_nonempty (d m : ℕ) : 0 < Fintype.card (Sample d m) :=
  Fintype.card_pos_iff.mpr ⟨fun _ => false⟩

/-- Direction check: a swap really transfers block 0 to block 1. -/
theorem swap_sample_block {m : ℕ} (ω : Sample 3 m) (a : UniformBlowup.Edge m) :
    sampleEquiv (Equiv.swap (0 : Fin 3) 1) ω (0,a) = ω (1,a) := by
  simp [sampleEquiv]

theorem swap_regular_block {k : ℕ} (ω : RegularSample 3 k) :
    regularSampleEquiv (Equiv.swap (0 : Fin 3) 1) ω 0 = ω 1 := by
  simp [regularSampleEquiv]

/-- Sample permutation is genuinely invertible at all dimensions. -/
theorem sample_roundtrip {d m : ℕ} (e : Equiv.Perm (Fin d)) (ω : Sample d m) :
    sampleEquiv e.symm (sampleEquiv e ω) = ω := by
  funext c
  simp

theorem regular_sample_roundtrip {d k : ℕ} (e : Equiv.Perm (Fin d))
    (ω : RegularSample d k) : regularSampleEquiv e.symm (regularSampleEquiv e ω) = ω := by
  funext i
  simp

/-- At order zero the actual unrooted successor cycle type is empty. -/
theorem cycle_empty_base (m : ℕ) : IsEmpty (Cycle 0 m) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨u, hu, _⟩ := σ.property.1
  exact Fin.elim0 u.1

theorem cycle_empty_blocks (d : ℕ) : IsEmpty (Cycle d 0) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨u, hu, _⟩ := σ.property.1
  exact Fin.elim0 u.2

theorem cycleCount_empty_base (T : Tournament 0) {m : ℕ} (ω : Sample 0 m) :
    cycleCount T ω = 0 := by
  let := cycle_empty_base m
  simp [cycleCount]

theorem cycleCount_empty_blocks {d : ℕ} (T : Tournament d) (ω : Sample d 0) :
    cycleCount T ω = 0 := by
  let := cycle_empty_blocks d
  simp [cycleCount]

end
end BaseRelabel
