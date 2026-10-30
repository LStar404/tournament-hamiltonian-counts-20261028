module

public import TournamentHamiltonian.BlockRatio.BaseLimit
public import TournamentHamiltonian.BlockRatio.Reindex

set_option autoImplicit false
@[expose] public section
open Filter Topology
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The deterministic ratio of the true uniform block density tends to the original constant.
Here d and the actual regular tournament are fixed; there is no joint-growth assertion. -/
theorem centered_rawRatio_tendsto {d : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hd : 0 < d) :
    Tendsto (fun m : ℕ => rawRatio (centered (m := m) T)) atTop
      (𝓝 (Real.exp 1 * spectralRatio T)) := by
  have hp := (baseShift_rawRatio_tendsto T hd).mul (scalarRatio_power_div_tendsto hd)
  rw [mul_comm (spectralRatio T)] at hp
  apply hp.congr'
  filter_upwards [eventually_order_ge d 20 hd] with m hm
  rw [centered_rawRatio_decomposition T hT hm]
  ring

/-- The same limit uses precisely the existing Gram-Gaussian expression. -/
theorem centered_det_gramGaussian_tendsto {d : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => Matrix.det (1 - centered (m := m) T) *
      gramGaussian (centered (m := m) T)) atTop (𝓝 (Real.exp 1 * spectralRatio T)) := by
  simpa only [rawRatio_eq_det_mul_gramGaussian] using centered_rawRatio_tendsto T hT hd

/-- The fixed-base limit at the `Fin (d*m)` interface consumed by dense-minor asymptotics. -/
theorem densityFin_det_gramGaussian_tendsto {d : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ =>
      Matrix.det (1 - (densityFin (m := m) T - averagingMatrix (Fin (d * m)))) *
        gramGaussian (densityFin (m := m) T - averagingMatrix (Fin (d * m))))
      atTop (𝓝 (Real.exp 1 * spectralRatio T)) := by
  simpa only [← rawRatio_eq_det_mul_gramGaussian, densityFin_centered_eq,
    rawRatio_submatrix_equiv] using centered_rawRatio_tendsto T hT hd

end
end UniformBlockMatrix
