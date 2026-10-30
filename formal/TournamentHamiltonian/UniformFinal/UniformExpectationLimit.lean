module

public import TournamentHamiltonian.UniformFinal.UniformDenseCountLimit
public import TournamentHamiltonian.UniformFinal.UniformNormalization

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
namespace UniformDenseLimit
open TournamentHamiltonian UniformFinalScalars

/-- The two independently constructed normalization interfaces are literally
the same actual expected-adjacency matrix with the same vertex relabelling. -/
theorem density_eq_uniformDensityFin {d m : ℕ} (T : Tournament d) :
    density (m := m) T = uniformDensityFin (m := m) T := rfl

/-- Actual finite uniform-model cycle expectations have the original fixed-base
spectral limit. The finite expectation bridge is used only eventually at N≥3. -/
theorem uniform_avgCycle_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => UniformBlowup.avgCycle (m := m) T /
      (((d*m-1).factorial : ℝ)/2^(d*m))) atTop (𝓝 (spectralRatio T)) := by
  have h := (cyclePrefactor_mul_tendsto d hd).mul (scaled_cycle_tendsto T hT hd)
  rw [exp_neg_one_mul_exp_one] at h
  have h' : Tendsto (fun m : ℕ => UniformBlowup.avgCycle (m := m) T / nu (d*m))
      atTop (𝓝 (spectralRatio T)) := by
    apply h.congr'
    filter_upwards [UniformBlockMatrix.eventually_order_ge d 3 hd] with m hm
    rw [uniform_avgCycle_normalization T hm, density_eq_uniformDensityFin]
    ring
  simpa only [nu] using h'

/-- Actual finite uniform-model path expectations have the same original
spectral limit, with the distinct N−1 path degree and N! normalization. -/
theorem uniform_avgPath_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => UniformBlowup.avgPath (m := m) T /
      (((d*m).factorial : ℝ)/2^(d*m-1))) atTop (𝓝 (spectralRatio T)) := by
  have h := (pathPrefactor_mul_tendsto d hd).mul (scaled_path_tendsto T hT hd)
  rw [exp_neg_one_mul_exp_one] at h
  have h' : Tendsto (fun m : ℕ => UniformBlowup.avgPath (m := m) T / mu (d*m))
      atTop (𝓝 (spectralRatio T)) := by
    apply h.congr'
    filter_upwards [UniformBlockMatrix.eventually_order_ge d 2 hd] with m hm
    rw [uniform_avgPath_normalization T hm, density_eq_uniformDensityFin]
    ring
  simpa only [mu] using h'

/-- Both uniform expected counts, with their actual finite normalizations,
converge simultaneously for every fixed genuine regular base tournament. -/
theorem uniform_expectations_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ =>
      (UniformBlowup.avgCycle (m := m) T / (((d*m-1).factorial : ℝ)/2^(d*m)),
       UniformBlowup.avgPath (m := m) T / (((d*m).factorial : ℝ)/2^(d*m-1))))
      atTop (𝓝 (spectralRatio T,spectralRatio T)) :=
  (uniform_avgCycle_tendsto T hT hd).prodMk_nhds (uniform_avgPath_tendsto T hT hd)

end UniformDenseLimit
