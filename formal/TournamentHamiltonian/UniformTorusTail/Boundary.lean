module

public import TournamentHamiltonian.UniformTorusTail.Endpoint

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The ε=1/16 window is the previously advertised m^(-7/16). -/
theorem window_one_sixteenth (m : ℕ) : window m (1/16) = (m : ℝ)^(-(7:ℝ)/16) := by
  unfold window
  congr 1
  norm_num

/-- No subset has a positive outlier count in zero dimension. -/
theorem outlierSets_zero : outlierSets 0 = ∅ := by
  ext B
  simp [outlierSets]

/-- A single outlier is included at the first allowed full dimension. -/
theorem one_outlier_included (i : Fin 64) : ({i} : Finset (Fin 64)) ∈ outlierSets 64 := by
  norm_num [outlierSets]

/-- The strict quarter cutoff is respected; the boundary r=m/4 is not included. -/
theorem quarter_outliers_excluded (B : Finset (Fin 64)) (hB : B.card=16) : B ∉ outlierSets 64 := by
  intro h
  have hlt := (Finset.mem_filter.mp h).2.2
  norm_num [hB] at hlt

theorem fifteen_outliers_included (B : Finset (Fin 64)) (hB : B.card=15) : B ∈ outlierSets 64 := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by omega, by norm_num [hB]⟩

/-- At m=64 a contributing near cluster has at least 49, not merely 8, vertices. -/
theorem first_dimension_cluster_size (B : Finset (Fin 64)) (hB : B∈outlierSets 64) : 49≤Bᶜ.card := by
  have hb := (Finset.mem_filter.mp hB).2.2
  have hc : B.card<16 := by exact_mod_cast (by norm_num at hb; exact hb)
  simp only [Finset.card_compl,Fintype.card_fin]
  omega

/-- Empty near-set factorization has exactly full m-dimensional mass π^m. -/
theorem selected_empty_factor (m : ℕ) (r : ℝ) :
    (∫ _x : Fin m → ℝ, (1:ℝ) ∂mixedMeasure (∅ : Finset (Fin m)) r) = Real.pi^m := by
  simp [mixedMeasure, integral_const, measureReal_def, Measure.pi_univ, cellMeasure, Real.pi_pos.le]


/-- Root-anchor real cube length zero has zero volume for every nonempty dimension. -/
theorem zero_width_cube (n : ℕ) (g : (Fin (n+1) → ℝ) → ℝ) :
    (∫ x, g x ∂cubeMeasure (n+1) 0 0) = 0 := by
  rw [cube_cons_integral]
  simp

/-- The exact far exponent at the first allowed size is -32κ₀. -/
theorem far_constant_64 : farConstant 64 = Real.exp (-32*kappa0) := by
  unfold farConstant
  congr 1
  norm_num
  ring

/-- No parity restriction enters the absolute-value torus-tail endpoint. -/
theorem prescribed_window_uniform :
    ∀ eta : ℝ, 0<eta → ∃ N : ℕ, ∀ n : ℕ, N≤n →
      ∀ H : SimpleGraph (Fin (n+1)), (∀ i, H.degree i≤2) →
        tailIntegral H (((n+1 : ℕ) : ℝ)^(-(7:ℝ)/16)) ≤ eta*Z (n+1) 1 := by
  simpa only [window_one_sixteenth] using uniform_deleted_torus_tail (1/16) (by norm_num)

end UniformTorusTail
