module

public import TournamentHamiltonian.RegularExpectation.Limits

@[expose] public section

set_option autoImplicit false
namespace RegularExpectation
open TournamentHamiltonian NonregularDecay Filter
open scoped Topology
noncomputable section
variable {d : ℕ}

theorem normalized_error {a b z ε : ℝ} (hz : 0<z) (h : |a-b|≤ε*b) :
    |a/z-b/z|≤ε*(b/z) := by
  rw [←sub_div,abs_div,abs_of_pos hz]
  calc |a-b|/z≤(ε*b)/z := div_le_div_of_nonneg_right h hz.le
    _ = _ := by ring


/-- The true regular/uniform cycle expectation ratio tends to the exponential correction. -/
theorem regular_uniform_cycle_ratio_tendsto (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgCycle T k/UniformBlowup.avgCycle (m:=2*k+1) T) atTop
      (𝓝 (Real.exp (1/(d:ℝ)))) := by
  apply WeightedMotif.tendsto_of_relative_errors ((MotifExp.cycle_exp_tendsto T hT hd).comp odd_size_tendsto)
  intro ε hε
  filter_upwards [ratio_exp_errors T hT hd ε hε] with k hk
  exact hk.1

theorem regular_uniform_path_ratio_tendsto (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgPath T k/UniformBlowup.avgPath (m:=2*k+1) T) atTop
      (𝓝 (Real.exp (1/(d:ℝ)))) := by
  apply WeightedMotif.tendsto_of_relative_errors ((MotifExp.path_exp_tendsto T hT hd).comp odd_size_tendsto)
  intro ε hε
  filter_upwards [ratio_exp_errors T hT hd ε hε] with k hk
  exact hk.2

/-- Actual regular-block unrooted-cycle expectation, at every admissible odd
block size m=2k+1, with the original factorial/2^N normalization. -/
theorem regular_avgCycle_tendsto (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgCycle T k/meanCycles (d*(2*k+1))) atTop
      (𝓝 (Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T)) := by
  apply WeightedMotif.tendsto_of_relative_errors (corrected_cycle_tendsto T hT hd)
  intro ε hε
  filter_upwards [actual_errors_eventually T hd ε hε] with k hk
  exact normalized_error (meanCycles_pos _) hk.1

/-- Actual regular-block path expectation, with the distinct N! / 2^(N-1)
normalization. No conditional containment or desired-limit premise is assumed. -/
theorem regular_avgPath_tendsto (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => regularAvgPath T k/meanPaths (d*(2*k+1))) atTop
      (𝓝 (Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T)) := by
  apply WeightedMotif.tendsto_of_relative_errors (corrected_path_tendsto T hT hd)
  intro ε hε
  filter_upwards [actual_errors_eventually T hd ε hε] with k hk
  exact normalized_error (path_mean_pos _) hk.2

theorem regular_expectations_tendsto (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => (regularAvgCycle T k/meanCycles (d*(2*k+1)),
      regularAvgPath T k/meanPaths (d*(2*k+1)))) atTop
      (𝓝 (Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T,
        Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T)) :=
  (regular_avgCycle_tendsto T hT hd).prodMk_nhds (regular_avgPath_tendsto T hT hd)

/-- The limiting constant is strictly positive for every positive base order. -/
theorem regular_limit_pos (T : Tournament d) (hd : 0<d) :
    0<Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T :=
  mul_pos (Real.exp_pos _) (spectralRatio_bounds T hd).1

end
end RegularExpectation
