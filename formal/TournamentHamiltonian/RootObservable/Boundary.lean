module

public import TournamentHamiltonian.RootObservable.Quartic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootObservable
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem jacobian_zero : jacobianFactor 0 = Real.sqrt (2*Real.pi) := by
  simp [jacobianFactor, modeMass]

theorem rootQuartic_one_vertex (F : EdgeSet 1) (x : Fin 0 → ℝ) : rootQuartic F x = 0 := by
  have hz : rootLift x = 0 := by
    ext i
    refine Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [rootQuartic, hz]

theorem rootCoordinates_one_vertex (y : Fin 1 → ℝ) : rootCoordinates y = 0 :=
  Subsingleton.elim _ _

theorem rootMatrix_empty_dimension (F : EdgeSet 1) : normalization (rootMatrix F) = 1 := by
  simp [normalization, Matrix.det_isEmpty]

theorem empty_dimension_weighted_integral (F : EdgeSet 1) (c : ℝ) :
    (∫ x : Fin 0 → ℝ, realKernel (rootMatrix F) 0 x*c) = c := by
  have hv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  simp [realKernel, dotProduct, measureReal_def, hv]

/-- The constant-mode factor is sqrt(2π), not 1, at a single vertex. -/
theorem one_vertex_weighted_integral (c : ℝ) :
    (∫ y : Fin 1 → ℝ, kernelDensity (emptyEdgeSet 1) y*c) = Real.sqrt (2*Real.pi)*c := by
  have hK : K (emptyEdgeSet 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [K, complement, emptyEdgeSet_laplacian, Matrix.one_apply]
  rw [integral_mul_const]
  unfold kernelDensity
  rw [hK, zero_integral Matrix.PosDef.one]
  simp [normalization]

/-- Actual empty-dimensional root observable, without imposing the asymptotic m≥16 guard. -/
theorem one_vertex_expDeviation_integral (F : EdgeSet 1) :
    (∫ x : Fin 0 → ℝ, realKernel (rootMatrix F) 0 x*rootExpDeviation F x) =
      |1-Real.exp (-(1/2 : ℝ))| := by
  have he (x : Fin 0 → ℝ) : rootExpDeviation F x = |1-Real.exp (-(1/2 : ℝ))| := by
    simp [rootExpDeviation, rootQuartic_one_vertex]
  simp_rw [he]
  exact empty_dimension_weighted_integral _ _

theorem rootCoordinates_two_vertices (y : Fin 2 → ℝ) :
    rootCoordinates y 0 = (y 1-y 0)/Real.sqrt 2 := by
  norm_num [rootCoordinates]

/-- A single retained unordered pair has coefficient 1/12, not 1/24 or 1/(12m²). -/
theorem rootQuartic_two_vertices (x : Fin 1 → ℝ) :
    rootQuartic (emptyEdgeSet 2) x = (x 0)^4/12 := by
  simp only [rootQuartic, Finset.sum_filter, emptyEdgeSet_graph]
  norm_num [Fin.sum_univ_succ, rootLift]

theorem root_kernel_two_vertices (x : Fin 1 → ℝ) :
    realKernel (rootMatrix (emptyEdgeSet 2)) 0 x = Real.exp (-(x 0)^2/2) := by
  rw [completeRoot_empty]
  have hq : x ⬝ᵥ completeRoot 1 *ᵥ x = (x 0)^2 := by
    norm_num [completeRoot, rootOnes, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_two]
  rw [realKernel, hq, zero_dotProduct, add_zero]

theorem phase_at_constant (n : ℕ) (F : EdgeSet (n+1)) (t : ℝ) :
    imbalance F ⬝ᵥ (fun _ => t) = 0 := by
  rw [dotProduct, ← Finset.sum_mul, sum_imbalance, zero_mul]

theorem cutoff_sixteen_root_bound (F : EdgeSet 16) :
    (∫ x : Fin 15 → ℝ, realKernel (rootMatrix F) 0 x * rootExpDeviation F x) /
      normalization (rootMatrix F) ≤ Real.exp 4*(Real.sqrt (3/16)+Real.sqrt 1680/192) := by
  have h := root_expDeviation_bound F (by norm_num : 16 ≤ 15+1)
  norm_num [errorRate] at h ⊢
  exact h

theorem one_vertex_normalized_transport (c : ℝ) :
    (∫ y : Fin 1 → ℝ, kernelDensity (emptyEdgeSet 1) y*c) / Real.sqrt (2*Real.pi) =
      ∫ x : Fin 0 → ℝ, realKernel (rootMatrix (emptyEdgeSet 1)) 0 x*c := by
  rw [one_vertex_weighted_integral, empty_dimension_weighted_integral]
  exact mul_div_cancel_left₀ c (by positivity)
end RootObservable
