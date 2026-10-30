module

public import TournamentHamiltonian.RegularExpectation.Endpoint
public import TournamentHamiltonian.FiniteFamilyGap.Finite
public import TournamentHamiltonian.UniformFinal.UniformExpectationLimit
public import Tournament.AsymptoticTransfer

@[expose] public section

set_option autoImplicit false
namespace FiniteExtremum
open TournamentHamiltonian UniformBlowup NonregularDecay RegularOrientation FiniteFamilyGap Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual normalized uniform cycle limit for every base, including nonregular bases. -/
theorem uniform_cycle_limit {d : ℕ} (T : Tournament d) (hd : 0<d) :
    Tendsto (fun m : ℕ => avgCycle (m:=m) T / meanCycles (d*m))
      atTop (𝓝 (uniformScore T)) := by
  by_cases hr : IsRegular T
  · rw [uniformScore_of_regular T hr]
    exact UniformDenseLimit.uniform_avgCycle_tendsto T hr hd
  · rw [uniformScore_of_nonregular T hr]
    exact uniform_avgCycle_tendsto_zero hd T hr

theorem uniform_path_limit {d : ℕ} (T : Tournament d) (hd : 0<d) :
    Tendsto (fun m : ℕ => avgPath (m:=m) T / meanPaths (d*m))
      atTop (𝓝 (uniformScore T)) := by
  by_cases hr : IsRegular T
  · rw [uniformScore_of_regular T hr]
    exact UniformDenseLimit.uniform_avgPath_tendsto T hr hd
  · rw [uniformScore_of_nonregular T hr]
    exact uniform_avgPath_tendsto_zero hd T hr

/-- Actual regular cycle limit, on precisely the admissible block sizes 2k+1. -/
theorem regular_cycle_limit {d : ℕ} (T : Tournament d) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgCycle T k / meanCycles (d*(2*k+1)))
      atTop (𝓝 (regularScore T)) := by
  by_cases hr : IsRegular T
  · rw [regularScore, uniformScore_of_regular T hr]
    exact RegularExpectation.regular_avgCycle_tendsto T hr hd
  · rw [regularScore_of_nonregular T hr]
    exact regular_avgCycle_tendsto_zero hd T hr

theorem regular_path_limit {d : ℕ} (T : Tournament d) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgPath T k / meanPaths (d*(2*k+1)))
      atTop (𝓝 (regularScore T)) := by
  by_cases hr : IsRegular T
  · rw [regularScore, uniformScore_of_regular T hr]
    exact RegularExpectation.regular_avgPath_tendsto T hr hd
  · rw [regularScore_of_nonregular T hr]
    exact regular_avgPath_tendsto_zero hd T hr

/-- The path normalizer is strictly positive even at zero order; its role is
only removing a common positive denominator, not asserting zero-size asymptotics. -/
theorem meanPaths_pos (n : ℕ) : 0 < meanPaths n := by
  unfold meanPaths
  positivity

end
end FiniteExtremum
