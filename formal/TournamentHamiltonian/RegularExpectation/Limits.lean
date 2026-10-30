module

public import TournamentHamiltonian.RegularExpectation.Averages
public import TournamentHamiltonian.UniformFinal.UniformExpectationLimit

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RegularExpectation
open BlockMotif TripleContraction FiniteMotif TournamentHamiltonian UniformBlowup NonregularDecay
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem path_mean_pos (n : ℕ) : 0<meanPaths n := by unfold meanPaths; positivity

theorem actual_positive_odd (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    ∀ᶠk : ℕ in atTop,3≤d*(2*k+1) ∧
      0<WeightedMotif.total (WeightedMotif.cycleWeight (m:=2*k+1) T) ∧
      0<WeightedMotif.total (WeightedMotif.pathWeight (m:=2*k+1) T) := by
  filter_upwards [odd_size_tendsto.eventually (UniformBlockMatrix.eventually_order_ge d 3 hd),
    odd_size_tendsto.eventually (WeightedMotif.actual_positive T hT hd)] with k hk hz
  exact ⟨hk,hz⟩

theorem actual_errors_eventually (T : Tournament d) (hd : 0<d) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠk : ℕ in atTop,
      |regularAvgCycle T k-cycleCorrected T (2*k+1)|≤ε*cycleCorrected T (2*k+1) ∧
      |regularAvgPath T k-pathCorrected T (2*k+1)|≤ε*pathCorrected T (2*k+1) := by
  obtain ⟨M,hM⟩ := actual_error_threshold d ε hε
  filter_upwards [odd_size_tendsto.eventually (eventually_ge_atTop M),
    odd_size_tendsto.eventually (UniformBlockMatrix.eventually_order_ge d 3 hd)] with k hk hn
  exact ⟨(hM k hk T).2 hn,(hM k hk T).1⟩

/-- This intermediate numerical approximation divides only by the positive true
uniform Hamilton partition, never by a permanent or individual candidate weight. -/
theorem ratio_exp_errors (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠk : ℕ in atTop,
      |regularAvgCycle T k/avgCycle (m:=2*k+1) T-MotifExp.cycleExp (m:=2*k+1) T|≤
        ε*MotifExp.cycleExp (m:=2*k+1) T ∧
      |regularAvgPath T k/avgPath (m:=2*k+1) T-MotifExp.pathExp (m:=2*k+1) T|≤
        ε*MotifExp.pathExp (m:=2*k+1) T := by
  filter_upwards [actual_positive_odd T hT hd,actual_errors_eventually T hd ε hε] with k hz he
  have hc : 0<avgCycle (m:=2*k+1) T := by simpa only [cycle_total_uniform T hz.1] using hz.2.1
  have hp : 0<avgPath (m:=2*k+1) T := by simpa only [path_total_uniform T] using hz.2.2
  rw [cycleCorrected_eq T hz.1 hz.2.1] at he
  rw [pathCorrected_eq T hz.2.2] at he
  have bound {a z e : ℝ} (hz : 0<z) (h : |a-z*e|≤ε*(z*e)) : |a/z-e|≤ε*e := by
    have hh := (div_le_div_iff_of_pos_right hz).mpr h
    have heq : a/z-e=(a-z*e)/z := by field_simp
    rw [heq,abs_div,abs_of_pos hz]
    convert hh using 1
    field_simp
  exact ⟨bound hc he.1,bound hp he.2⟩

theorem corrected_cycle_tendsto (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => cycleCorrected T (2*k+1)/meanCycles (d*(2*k+1))) atTop
      (𝓝 (Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T)) := by
  have hu := (UniformDenseLimit.uniform_avgCycle_tendsto T hT hd).comp odd_size_tendsto
  have he := (MotifExp.cycle_exp_tendsto T hT hd).comp odd_size_tendsto
  have h := he.mul hu
  apply h.congr'
  filter_upwards [actual_positive_odd T hT hd] with k hk
  rw [cycleCorrected_eq T hk.1 hk.2.1]
  change MotifExp.cycleExp (m:=2*k+1) T*(avgCycle (m:=2*k+1) T/meanCycles (d*(2*k+1))) = (avgCycle (m:=2*k+1) T*MotifExp.cycleExp (m:=2*k+1) T)/meanCycles (d*(2*k+1))
  ring

theorem corrected_path_tendsto (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun k : ℕ => pathCorrected T (2*k+1)/meanPaths (d*(2*k+1))) atTop
      (𝓝 (Real.exp (1/(d:ℝ))*TournamentHamiltonian.spectralRatio T)) := by
  have hu := (UniformDenseLimit.uniform_avgPath_tendsto T hT hd).comp odd_size_tendsto
  have he := (MotifExp.path_exp_tendsto T hT hd).comp odd_size_tendsto
  have h := he.mul hu
  apply h.congr'
  filter_upwards [actual_positive_odd T hT hd] with k hk
  rw [pathCorrected_eq T hk.2.2]
  change MotifExp.pathExp (m:=2*k+1) T*(avgPath (m:=2*k+1) T/meanPaths (d*(2*k+1))) = (avgPath (m:=2*k+1) T*MotifExp.pathExp (m:=2*k+1) T)/meanPaths (d*(2*k+1))
  ring

end
end RegularExpectation
