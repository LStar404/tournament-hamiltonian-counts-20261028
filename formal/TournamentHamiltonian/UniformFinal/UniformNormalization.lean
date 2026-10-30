module

public import TournamentHamiltonian.UniformFinal.CountingNormalization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace UniformFinalScalars
open TournamentHamiltonian WeightedCycle
open Filter Topology
open scoped Classical
noncomputable section

/-- The genuine cycle count is invariant under vertex relabelling. This uses
its exact finite convolution, not a new orbit-counting axiom. -/
theorem cyc_submatrix_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty α] (e : α ≃ β) (A : Matrix β β ℝ) :
    cyc (A.submatrix e e) = cyc A := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hn
  rw [convolution, Fintype.card_congr e, convolution]
  congr 1
  apply Fintype.sum_equiv e.finsetCongr
  intro U
  let ep : U ≃ e.finsetCongr U :=
    e.subtypeEquiv (fun i => by simp [Equiv.finsetCongr_apply])
  let en : (Uᶜ : Finset α) ≃ ((e.finsetCongr U)ᶜ : Finset β) :=
    e.subtypeEquiv (fun i => by simp [Equiv.finsetCongr_apply])
  have hp : ((-(A.submatrix e e)).submatrix
      (Subtype.val : U → α) Subtype.val).det =
      ((-A).submatrix (Subtype.val : e.finsetCongr U → β) Subtype.val).det :=
    Matrix.det_submatrix_equiv_self ep
      ((-A).submatrix (Subtype.val : e.finsetCongr U → β) Subtype.val)
  have hc : U.card = (e.finsetCongr U).card := by simp [Equiv.finsetCongr_apply]
  have hm : ((A.submatrix e e).submatrix
      (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent =
      (A.submatrix (Subtype.val : ((e.finsetCongr U)ᶜ : Finset β) → β)
        Subtype.val).permanent :=
    permanent_submatrix_equiv_self
      (A.submatrix (Subtype.val : ((e.finsetCongr U)ᶜ : Finset β) → β) Subtype.val) en
  rw [hp, hc, hm]

theorem path_submatrix_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (A : Matrix β β ℝ) :
    path (A.submatrix e e) = path A := by
  rw [path_convolution, path_convolution]
  exact complementConvolution_submatrix_equiv e A

/-- Exact stochastic normalization of the actual uniform finite-cube weights. -/
def uniformDensity {d m : ℕ} (T : Tournament d) :
    Matrix (UniformBlowup.Vertex d m) (UniformBlowup.Vertex d m) ℝ :=
  (2 / ((d*m : ℕ) - 1 : ℝ)) • UniformBlowup.weight T

theorem uniformDensity_eq_matrix_smul {d m : ℕ} (T : Tournament d) :
    uniformDensity (m := m) T = (2 / ((d*m : ℕ) - 1 : ℝ)) •
      (UniformBlowup.weight T : Matrix (UniformBlowup.Vertex d m) (UniformBlowup.Vertex d m) ℝ) := by
  ext i j
  rfl

def uniformDensityFin {d m : ℕ} (T : Tournament d) :
    Matrix (Fin (d*m)) (Fin (d*m)) ℝ :=
  (uniformDensity (m := m) T).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Actual model expectation, correct unrooted-cycle normalization, and the
same Fin-labelled density used by the frozen block-ratio theorem. -/
theorem uniform_avgCycle_normalization {d m : ℕ} (T : Tournament d) (hN : 3 ≤ d*m) :
    UniformBlowup.avgCycle (m := m) T / nu (d*m) =
      cyclePrefactor (d*m) *
        ((d*m : ℕ)^ (d*m) / ((d*m).factorial : ℝ) * (d*m : ℕ) *
          cyc (uniformDensityFin (m := m) T)) := by
  have : Nonempty (Fin (d*m)) := Fin.pos_iff_nonempty.mp (by omega)
  rw [uniformDensityFin, cyc_submatrix_equiv]
  rw [UniformBlowup.avgCycle_eq_weightedCycleSum hN,
    ← cyc_eq_uniform_weightedCycleSum (by omega)]
  have hcard : 2 ≤ Fintype.card (UniformBlowup.Vertex d m) := by simpa using (show 2 ≤ d*m by omega)
  rw [uniformDensity_eq_matrix_smul]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    cyc_density_restoration (UniformBlowup.weight (m := m) T) hcard

/-- Paths use exponent N−1 and the stochastic count divided by N, not the
cycle normalization. N≥2 is only needed to invert the density scale. -/
theorem uniform_avgPath_normalization {d m : ℕ} (T : Tournament d) (hN : 2 ≤ d*m) :
    UniformBlowup.avgPath (m := m) T / mu (d*m) =
      pathPrefactor (d*m) *
        ((d*m : ℕ)^ (d*m) / ((d*m).factorial : ℝ) *
          path (uniformDensityFin (m := m) T) / (d*m : ℕ)) := by
  rw [uniformDensityFin, path_submatrix_equiv]
  rw [← path_eq_uniform_avgPath T]
  have hcard : 2 ≤ Fintype.card (UniformBlowup.Vertex d m) := by simpa using hN
  rw [uniformDensity_eq_matrix_smul]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    path_density_restoration (UniformBlowup.weight (m := m) T) hcard

/-- No surrogate matrix: this is precisely the previously certified dense
class membership for actual uniform weights after the same labelling. -/
theorem uniformDensityFin_denseStochastic {d m : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hN : 20 ≤ d*m) :
    DenseStochastic (uniformDensityFin (m := m) T) :=
  UniformBlockMatrix.uniform_densityFin_denseStochastic T hT hN

/-- The frozen block-ratio limit, exposed with this exact normalization object. -/
theorem uniformDensityFin_ratio_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ =>
      Matrix.det (1 - (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m)))) *
        gramGaussian (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m)))) atTop
      (𝓝 (Real.exp 1 * spectralRatio T)) :=
  UniformBlockMatrix.uniform_weightFin_ratio_tendsto T hT hd

/-- The deterministic block-ratio factor with the cycle normalization already
has the intended spectral limit. This is not a counting asymptotic. -/
theorem uniform_cycle_ratio_factor_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => cyclePrefactor (d*m) *
      (Matrix.det (1 - (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m)))) *
        gramGaussian (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m))))) atTop
      (𝓝 (spectralRatio T)) := by
  have h := (cyclePrefactor_mul_tendsto d hd).mul (uniformDensityFin_ratio_tendsto T hT hd)
  simpa only [exp_neg_one_mul_exp_one] using h

theorem uniform_path_ratio_factor_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    Tendsto (fun m : ℕ => pathPrefactor (d*m) *
      (Matrix.det (1 - (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m)))) *
        gramGaussian (uniformDensityFin (m := m) T - averagingMatrix (Fin (d*m))))) atTop
      (𝓝 (spectralRatio T)) := by
  have h := (pathPrefactor_mul_tendsto d hd).mul (uniformDensityFin_ratio_tendsto T hT hd)
  simpa only [exp_neg_one_mul_exp_one] using h

end
end UniformFinalScalars
