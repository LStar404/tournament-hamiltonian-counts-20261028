module

public import TournamentHamiltonian.BlockRatio.ScalarLimit

set_option autoImplicit false
@[expose] public section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Only the dimension of the base matrix is fixed; block size ranges over all naturals. -/
theorem baseShift_tendsto_normalized_sign {d : ℕ} (T : Tournament d) (hd : 0 < d) :
    Tendsto (fun m : ℕ => baseShift (m := m) T) atTop
      (𝓝 (((1 : ℝ) / d) • signMatrix T)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have ht := ((mul_blockStep_tendsto hd).mul_const (signMatrix T i j)).sub
    ((blockStep_tendsto_zero hd).mul_const ((1 : Matrix (Fin d) (Fin d) ℝ) i j))
  simp only [zero_mul, sub_zero] at ht
  convert ht using 1
  · funext m
    simp only [baseShift, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
    ring

/-- Continuity is used only at matrices with an actually positive Gram determinant. -/
theorem continuousAt_rawRatio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℝ) (hZ : 0 < Matrix.det (1 - Z.transpose * Z)) :
    ContinuousAt rawRatio Z := by
  have hn : Continuous (fun X : Matrix ι ι ℝ => Matrix.det (1 - X)) := by fun_prop
  have hd : Continuous (fun X : Matrix ι ι ℝ => Real.sqrt (Matrix.det (1 - X.transpose * X))) := by
    fun_prop
  exact hn.continuousAt.div hd.continuousAt (Real.sqrt_pos.mpr hZ).ne'

/-- The full base-shift ratio converges to the library's original spectralRatio. -/
theorem baseShift_rawRatio_tendsto {d : ℕ} (T : Tournament d) (hd : 0 < d) :
    Tendsto (fun m : ℕ => rawRatio (baseShift (m := m) T)) atTop (𝓝 (spectralRatio T)) := by
  have hc := continuousAt_rawRatio (((1 : ℝ) / d) • signMatrix T)
    (normalized_sign_gram_det_pos T hd)
  have ht := hc.tendsto.comp (baseShift_tendsto_normalized_sign T hd)
  simpa only [Function.comp_def, rawRatio_normalized_sign_eq_spectralRatio] using ht

end
end UniformBlockMatrix
