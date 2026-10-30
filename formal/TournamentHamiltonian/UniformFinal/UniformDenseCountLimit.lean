module

public import TournamentHamiltonian.DenseScaleConvergence
public import TournamentHamiltonian.BlockRatio.UniformLimit

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
namespace UniformDenseLimit
open TournamentHamiltonian

/-- The actual uniform expected adjacency, normalized and exactly relabelled;
this is not an abstract matrix family satisfying an assumed asymptotic. -/
noncomputable def density {d m : ℕ} (T : Tournament d) :
    Matrix (Fin (d*m)) (Fin (d*m)) ℝ :=
  Matrix.submatrix ((2/((d*m : ℕ)-1 : ℝ)) •
    (UniformBlowup.weight T : Matrix (UniformBlockMatrix.Vertex d m) (UniformBlockMatrix.Vertex d m) ℝ))
      finProdFinEquiv.symm finProdFinEquiv.symm

/-- Actual fixed-base uniform model inserted into the unconditional dense
count error theorem; no model-specific asymptotic input is assumed. -/
theorem scaled_errors_tendsto {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => (((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
      (((d*m : ℕ) : ℝ)*WeightedCycle.cyc (density (m := m) T))-
        (1-denseBaseKernel (density (m := m) T)).det*gramGaussian (denseBaseKernel (density (m := m) T)))
      atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => (((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
      (WeightedCycle.path (density (m := m) T)/((d*m : ℕ) : ℝ))-
        (1-denseBaseKernel (density (m := m) T)).det*gramGaussian (denseBaseKernel (density (m := m) T)))
      atTop (𝓝 0) := by
  have hε : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |(((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
        (((d*m : ℕ) : ℝ)*WeightedCycle.cyc (density (m := m) T))-
          (1-denseBaseKernel (density (m := m) T)).det*gramGaussian (denseBaseKernel (density (m := m) T))| < ε ∧
      |(((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
        (WeightedCycle.path (density (m := m) T)/((d*m : ℕ) : ℝ))-
          (1-denseBaseKernel (density (m := m) T)).det*gramGaussian (denseBaseKernel (density (m := m) T))| < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (dense_scaled_cycle_path_errors_uniform_tendsto ε hε)
    filter_upwards [UniformBlockMatrix.eventually_order_ge d (max 20 N) hd] with m hm
    exact hN (d*m) ((le_max_right _ _).trans hm) (density T)
      (UniformBlockMatrix.uniform_densityFin_denseStochastic T hT ((le_max_left _ _).trans hm))
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [hε ε he] with m hm
    simpa only [Real.dist_eq,sub_zero] using hm.1
  · apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [hε ε he] with m hm
    simpa only [Real.dist_eq,sub_zero] using hm.2

/-- Actual block-ratio limit, stated in the exact normalized-weight interface. -/
theorem main_term_tendsto {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => (1-denseBaseKernel (density (m := m) T)).det*
      gramGaussian (denseBaseKernel (density (m := m) T)))
      atTop (𝓝 (Real.exp 1*spectralRatio T)) := by
  exact UniformBlockMatrix.uniform_weightFin_ratio_tendsto T hT hd

/-- True normalized-density cycle count, before the final scalar restoration. -/
theorem scaled_cycle_tendsto {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => (((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
      (((d*m : ℕ) : ℝ)*WeightedCycle.cyc (density (m := m) T)))
      atTop (𝓝 (Real.exp 1*spectralRatio T)) := by
  have h := (scaled_errors_tendsto T hT hd).1.add (main_term_tendsto T hT hd)
  simpa only [sub_add_cancel,zero_add] using h

theorem scaled_path_tendsto {d : ℕ} (T : Tournament d) (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => (((d*m : ℕ) : ℝ)^(d*m)/((d*m).factorial : ℝ))*
      (WeightedCycle.path (density (m := m) T)/((d*m : ℕ) : ℝ)))
      atTop (𝓝 (Real.exp 1*spectralRatio T)) := by
  have h := (scaled_errors_tendsto T hT hd).2.add (main_term_tendsto T hT hd)
  simpa only [sub_add_cancel,zero_add] using h

end UniformDenseLimit
