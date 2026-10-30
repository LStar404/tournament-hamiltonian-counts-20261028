module

public import TournamentHamiltonian.NonregularDecay.CycleDecay

@[expose] public section

set_option autoImplicit false

namespace NonregularDecay
open TournamentHamiltonian UniformBlowup RegularOrientation Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Elementary finite averaging, with its nonempty sample-space obligation explicit. -/
theorem finite_average_le {α : Type*} [Fintype α] (hα : 0 < Fintype.card α)
    (f : α → ℝ) (q : ℝ) (hf : ∀ x, f x ≤ q) :
    (∑ x, f x) / Fintype.card α ≤ q := by
  apply (div_le_iff₀ (by exact_mod_cast hα : (0 : ℝ) < Fintype.card α)).mpr
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => hf x)
  simpa [mul_comm] using h

/-- The genuine equal-weight expectation over independent uniform regular blocks,
indexed by all admissible sizes m=2k+1. -/
def regularAvgPath {d : ℕ} (T : Tournament d) (k : ℕ) : ℝ :=
  (∑ ω : RegularSample d k, (pathCount T (regularSampleBits ω) : ℝ)) /
    Fintype.card (RegularSample d k)

def regularAvgCycle {d : ℕ} (T : Tournament d) (k : ℕ) : ℝ :=
  (∑ ω : RegularSample d k, (cycleCount T (regularSampleBits ω) : ℝ)) /
    Fintype.card (RegularSample d k)

/-- The regular expectation averages the old actual tournament path count,
not a newly postulated random variable. -/
theorem regularAvgPath_eq_existing {d : ℕ} (T : Tournament d) (k : ℕ)
    (e : Arrangement d (2*k+1)) :
    regularAvgPath T k =
      (∑ ω : RegularSample d k, (TournamentHamiltonian.pathCount (regularBlowup T ω e) : ℝ)) /
        Fintype.card (RegularSample d k) := by
  unfold regularAvgPath regularBlowup
  simp_rw [← pathCount_eq_existing T _ e]

theorem uniform_avgPath_eventually_small {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, avgPath (m := m) T / meanPaths (d*m) ≤ ε / (d*m) := by
  filter_upwards [path_eventually_small hd T hT hε] with m hm
  rw [avgPath, div_right_comm, Finset.sum_div]
  apply finite_average_le (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  exact hm

theorem uniform_avgCycle_eventually_le {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    ∀ᶠ m : ℕ in atTop, avgCycle (m := m) T / meanCycles (d*m) ≤ cycleMajorant (d*m) := by
  filter_upwards [cycle_eventually_le_majorant hd T hT] with m hm
  rw [avgCycle, div_right_comm, Finset.sum_div]
  apply finite_average_le (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  exact hm

/-- §11 nonregular-base uniform-block normalized path limit. -/
theorem uniform_avgPath_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    Tendsto (fun m => avgPath (m := m) T / meanPaths (d*m)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m : ℕ => (1 : ℝ)/(d*m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (order_tendsto hd)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun m => by unfold avgPath meanPaths; positivity
  · exact uniform_avgPath_eventually_small hd T hT (by norm_num)

/-- §11 nonregular-base uniform-block normalized unrooted-cycle limit. -/
theorem uniform_avgCycle_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    Tendsto (fun m => avgCycle (m := m) T / meanCycles (d*m)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (cycleMajorant_tendsto_zero.comp (order_tendsto hd))
  · exact Filter.Eventually.of_forall fun m => by unfold avgCycle meanCycles; positivity
  · exact uniform_avgCycle_eventually_le hd T hT

theorem odd_size_tendsto : Tendsto (fun k : ℕ => 2*k+1) atTop atTop := by
  apply tendsto_atTop_mono (fun k => show k ≤ 2*k+1 by omega) tendsto_id

theorem regular_avgPath_eventually_small {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      regularAvgPath T k / meanPaths (d*(2*k+1)) ≤ ε / (d*(2*k+1)) := by
  filter_upwards [odd_size_tendsto.eventually (path_eventually_small hd T hT hε)] with k hk
  rw [regularAvgPath, div_right_comm, Finset.sum_div]
  apply finite_average_le (regularSample_card_pos d k)
  intro ω
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hk (regularSampleBits ω)

theorem regular_avgCycle_eventually_le {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    ∀ᶠ k : ℕ in atTop,
      regularAvgCycle T k / meanCycles (d*(2*k+1)) ≤ cycleMajorant (d*(2*k+1)) := by
  filter_upwards [odd_size_tendsto.eventually (cycle_eventually_le_majorant hd T hT)] with k hk
  rw [regularAvgCycle, div_right_comm, Finset.sum_div]
  apply finite_average_le (regularSample_card_pos d k)
  intro ω
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hk (regularSampleBits ω)

/-- §11 nonregular-base regular-block normalized path limit, through odd sizes. -/
theorem regular_avgPath_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    Tendsto (fun k => regularAvgPath T k / meanPaths (d*(2*k+1))) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k : ℕ => (1 : ℝ)/(d*(2*k+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      tendsto_one_div_atTop_nhds_zero_nat.comp ((order_tendsto hd).comp odd_size_tendsto)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun k => by unfold regularAvgPath meanPaths; positivity
  · exact regular_avgPath_eventually_small hd T hT (by norm_num)

/-- §11 nonregular-base regular-block normalized unrooted-cycle limit. -/
theorem regular_avgCycle_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) :
    Tendsto (fun k => regularAvgCycle T k / meanCycles (d*(2*k+1))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (cycleMajorant_tendsto_zero.comp ((order_tendsto hd).comp odd_size_tendsto))
  · exact Filter.Eventually.of_forall fun k => by unfold regularAvgCycle meanCycles; positivity
  · exact regular_avgCycle_eventually_le hd T hT

end
end NonregularDecay
