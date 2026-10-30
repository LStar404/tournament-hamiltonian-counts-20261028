module

public import TournamentHamiltonian.DenseCycleConvergence
public import TournamentHamiltonian.DensePathHadamard
public import TournamentHamiltonian.WeightedCycle.PathIntegration

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
namespace TournamentHamiltonian

/-- The exact finite main term uses the same centering as the permanent analysis. -/
theorem dense_centered_eq_base {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    WeightedCycle.centered D = denseBaseKernel D := by
  ext i j
  simp [WeightedCycle.centered, WeightedCycle.constantProjection, denseBaseKernel, averagingMatrix]

/-- The actual path error, with the essential 1/n normalization, is bounded
by the same explicit budget as cycles. The complement is J-D, not I+D. -/
theorem DenseStochastic.path_error_le_budget {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ)) :
    |WeightedCycle.path D/((n : ℝ)*D.permanent)-(1-WeightedCycle.centered D).det| ≤
      ∑ k ∈ Finset.range (n+1), denseCountWeight k*denseRatioErrorBudget n k := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := WeightedCycle.abs_normalized_path_error_le D hD.row_sum
  simp only [Fintype.card_fin] at h
  apply h.trans
  rw [dense_sum_by_card, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ ≤ (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        |((Matrix.of (fun _ _ : Fin n => (1 : ℝ))-D).submatrix
          (Subtype.val : U → Fin n) Subtype.val).det| * denseRatioErrorBudget n k)/(n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR
      apply Finset.sum_le_sum
      intro U hU
      have hc := (Finset.mem_powersetCard.mp hU).2
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [hc,densePrincipalMinor] using hD.minor_error_le_budget hn hlarge U
    _ = ((∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        |((Matrix.of (fun _ _ : Fin n => (1 : ℝ))-D).submatrix
          (Subtype.val : U → Fin n) Subtype.val).det|)/(n : ℝ))*denseRatioErrorBudget n k := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ denseCountWeight k*denseRatioErrorBudget n k :=
      mul_le_mul_of_nonneg_right (hD.path_layer_hadamard hn k) (denseRatioErrorBudget_nonneg n k)

/-- Uniform actual path-count error throughout the dense matrix class. -/
theorem dense_path_error_uniform_tendsto :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        |WeightedCycle.path D/((n : ℝ)*D.permanent)-(1-WeightedCycle.centered D).det| < ε := by
  intro ε hε
  have he := (Metric.tendsto_nhds.mp dense_count_budget_sum_tendsto) ε hε
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  filter_upwards [he, eventually_ge_atTop (max 1 N)] with n hn hnN
  intro D hD
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right _ _).trans hnN)
  have hb := hD.path_error_le_budget (by omega) (hN.trans hNn)
  exact hb.trans_lt ((le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn))

/-- Sequence form: no convergence of det(I-B_n) is required. -/
theorem dense_path_error_tendsto (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ᶠ n in atTop, DenseStochastic (D n)) :
    Tendsto (fun n : ℕ => WeightedCycle.path (D n)/((n : ℝ)*(D n).permanent)-
      (1-WeightedCycle.centered (D n)).det) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [dense_path_error_uniform_tendsto ε hε,hD] with n hn hDn
  simpa only [Real.dist_eq, sub_zero] using hn (D n) hDn

/-- Simultaneous epsilon-uniform endpoint for both actual finite counts, stated
with exactly the base kernel used by the permanent and Gram modules. -/
theorem dense_cycle_path_error_uniform_tendsto :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        |(n : ℝ)*WeightedCycle.cyc D/D.permanent-(1-denseBaseKernel D).det| < ε ∧
        |WeightedCycle.path D/((n : ℝ)*D.permanent)-(1-denseBaseKernel D).det| < ε := by
  intro ε hε
  filter_upwards [dense_cycle_error_uniform_tendsto ε hε,
    dense_path_error_uniform_tendsto ε hε] with n hc hp
  intro D hD
  simpa only [dense_centered_eq_base] using And.intro (hc D hD) (hp D hD)

end TournamentHamiltonian
