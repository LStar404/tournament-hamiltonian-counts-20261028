module

public import TournamentHamiltonian.LocalLogCos.Integral
public import TournamentHamiltonian.RootObservable.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral RootObservable PDGaussian Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem remainder_zero : remainder 0 = 0 := by norm_num [remainder,logCos]

theorem derivatives_at_zero :
    iteratedDeriv 1 logCos 0 = 0 ∧ iteratedDeriv 2 logCos 0 = -1 ∧
    iteratedDeriv 4 logCos 0 = -2 ∧ iteratedDeriv 6 logCos 0 = -16 := by
  norm_num [iteratedDeriv_logCos, jet]

theorem sixth_at_quarter : iteratedDeriv 6 logCos (Real.pi/4) = -512 := by
  rw [iteratedDeriv_logCos 6 (by omega)
    (cos_pos_of_abs_le_quarter (by rw [abs_of_nonneg (by positivity)])).ne']
  norm_num [jet,Real.tan_pi_div_four]

theorem positive_endpoint : -(Real.pi/4)^6 ≤ remainder (Real.pi/4) ∧ remainder (Real.pi/4) ≤ 0 := by
  simpa only [abs_of_nonneg (by positivity : (0:ℝ)≤Real.pi/4)] using
    remainder_bounds (x := Real.pi/4) (by rw [abs_of_nonneg (by positivity)])

theorem negative_endpoint : -(Real.pi/4)^6 ≤ remainder (-(Real.pi/4)) ∧ remainder (-(Real.pi/4)) ≤ 0 := by
  simpa only [remainder_even] using positive_endpoint

theorem one_vertex_cosProduct (F : EdgeSet 1) (x : Fin 0 → ℝ) : cosProduct F x = 1 := by
  have hz : rootLift x = 0 := by ext i; refine Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [cosProduct,hz]

theorem one_vertex_remainderSum (F : EdgeSet 1) (x : Fin 0 → ℝ) : remainderSum F x = 0 := by
  have hz : rootLift x = 0 := by ext i; refine Fin.cases rfl (fun j => Fin.elim0 j) i
  simp [remainderSum,hz,remainder_zero]

theorem two_vertex_cosProduct (x : Fin 1 → ℝ) : cosProduct (emptyEdgeSet 2) x = Real.cos (x 0) := by
  simp only [cosProduct, Finset.prod_filter, emptyEdgeSet_graph]
  norm_num [Fin.prod_univ_succ, rootLift]

theorem two_vertex_remainderSum (x : Fin 1 → ℝ) : remainderSum (emptyEdgeSet 2) x = remainder (x 0) := by
  simp only [remainderSum, Finset.sum_filter, emptyEdgeSet_graph]
  norm_num [Fin.sum_univ_succ, rootLift, remainder_even]

theorem two_vertex_expansion {r : ℝ} (hr : 0≤r) (hrp : r≤Real.pi/8)
    (x : Fin 1 → ℝ) (hx : |x 0|≤r) :
    Real.cos (x 0) = Real.exp (-(x 0)^2/2-(x 0)^4/12+remainder (x 0)) := by
  have hc : 0<Real.cos (x 0) := cos_pos_of_abs_le_quarter (by linarith [hr])
  rw [remainder,logCos]
  rw [show -(x 0)^2/2-(x 0)^4/12+(Real.log (Real.cos (x 0))+(x 0)^2/2+(x 0)^4/12) =
    Real.log (Real.cos (x 0)) by ring, Real.exp_log hc]

theorem errorBudget_at_zero (m : ℕ) : errorBudget m 0 = 0 := by simp [errorBudget]
theorem cutoff_one : cutoff 1 = 1 := by norm_num [cutoff]
theorem cutoffError_one : cutoffError 1 = 32 := by norm_num [cutoffError]
theorem fixed_cutoff_exponent_test : errorBudget 16 (cutoff 16) = 32*(16:ℝ)^(-(5/8:ℝ)) :=
  errorBudget_cutoff 16 (by norm_num)
end LocalLogCos
