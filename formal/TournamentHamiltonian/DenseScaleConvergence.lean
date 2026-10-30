module

public import TournamentHamiltonian.DenseScaleBounds

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
namespace TournamentHamiltonian

/-- Quantitative bounded-product transfer; both varying multipliers are bounded. -/
theorem dense_scale_error_transfer (p q d g P M E B : ℝ)
    (hp : |p| ≤ P) (hq : |q-d| ≤ B) (hd : |d| ≤ M) (he : |p-g| ≤ E) :
    |p*q-d*g| ≤ P*B+M*E := by
  calc
    _ = |p*(q-d)+d*(p-g)| := by congr 1; ring
    _ ≤ |p*(q-d)|+|d*(p-g)| := abs_add_le _ _
    _ = |p| *|q-d|+|d| *|p-g| := by rw [abs_mul,abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul hp hq (abs_nonneg _) ((abs_nonneg _).trans hp))
      (mul_le_mul hd he (abs_nonneg _) ((abs_nonneg _).trans hd))

noncomputable def denseScaleErrorBudget (n : ℕ) : ℝ :=
  denseScaledPermanentBound*(∑ k ∈ Finset.range (n+1), denseCountWeight k*denseRatioErrorBudget n k)+
    (denseDeterminantBound*denseGaussianBound*denseFullPermanentConstant)/n

theorem denseScaleErrorBudget_tendsto :
    Tendsto denseScaleErrorBudget atTop (𝓝 0) := by
  have hh := (dense_count_budget_sum_tendsto.const_mul denseScaledPermanentBound).add
    (tendsto_natCast_atTop_atTop.const_div_atTop
      (denseDeterminantBound*denseGaussianBound*denseFullPermanentConstant))
  unfold denseScaleErrorBudget
  simpa only [mul_zero,add_zero] using hh

/-- Real factorial-scaled cycle and path errors: all varying-factor bounds have
been proved, rather than inferred from the permanent's relative error alone. -/
theorem DenseStochastic.scaled_count_errors_le_budget {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ)) :
    |((n : ℝ)^n/(n.factorial : ℝ))*((n : ℝ)*WeightedCycle.cyc D)-
      (1-denseBaseKernel D).det*gramGaussian (denseBaseKernel D)| ≤ denseScaleErrorBudget n ∧
    |((n : ℝ)^n/(n.factorial : ℝ))*(WeightedCycle.path D/n)-
      (1-denseBaseKernel D).det*gramGaussian (denseBaseKernel D)| ≤ denseScaleErrorBudget n := by
  have hlarge' : 2*denseFullPermanentConstant ≤ (n : ℝ) := by
    linarith [densePermanentConstants_nonneg.1,densePermanentConstants_nonneg.2]
  have hDp := (hD.minor_ratio_le_exp_ambient hn hlarge' ∅).1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp := hD.scaled_permanent_uniform_bound hn
  have hd := hD.centered_det_uniform_bound hn
  have he := hD.scaled_permanent_error_bound hn
  have hc := hD.cycle_error_le_budget hn hlarge
  have hh := hD.path_error_le_budget hn hlarge
  rw [dense_centered_eq_base] at hc hh
  have hc' := dense_scale_error_transfer _ _ _ _ _ _ _ _ hp hc hd he
  have hh' := dense_scale_error_transfer _ _ _ _ _ _ _ _ hp hh hd he
  constructor
  · convert hc' using 1
    · congr 1
      field_simp
    · unfold denseScaleErrorBudget
      ring
  · convert hh' using 1
    · congr 1
      field_simp
    · unfold denseScaleErrorBudget
      ring

/-- Uniformly in the actual dense class, the cycle and path factorial-scaled
counts have main term det(I-B) times its genuine Gram Gaussian. -/
theorem dense_scaled_cycle_path_errors_uniform_tendsto :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        |((n : ℝ)^n/(n.factorial : ℝ))*((n : ℝ)*WeightedCycle.cyc D)-
          (1-denseBaseKernel D).det*gramGaussian (denseBaseKernel D)| < ε ∧
        |((n : ℝ)^n/(n.factorial : ℝ))*(WeightedCycle.path D/n)-
          (1-denseBaseKernel D).det*gramGaussian (denseBaseKernel D)| < ε := by
  intro ε hε
  have he := (Metric.tendsto_nhds.mp denseScaleErrorBudget_tendsto) ε hε
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  filter_upwards [he,eventually_ge_atTop (max 1 N)] with n hn hnN
  intro D hD
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right _ _).trans hnN)
  have hb := hD.scaled_count_errors_le_budget (by omega) (hN.trans hNn)
  have he' : denseScaleErrorBudget n < ε :=
    (le_abs_self _).trans_lt (by simpa only [Real.dist_eq,sub_zero] using hn)
  exact ⟨hb.1.trans_lt he',hb.2.trans_lt he'⟩

/-- Sequence variant with no additional asymptotic hypotheses. -/
theorem dense_scaled_cycle_error_tendsto (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ᶠ n in atTop, DenseStochastic (D n)) :
    Tendsto (fun n : ℕ => ((n : ℝ)^n/(n.factorial : ℝ))*((n : ℝ)*WeightedCycle.cyc (D n))-
      (1-denseBaseKernel (D n)).det*gramGaussian (denseBaseKernel (D n))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [dense_scaled_cycle_path_errors_uniform_tendsto ε hε,hD] with n hn hDn
  simpa only [Real.dist_eq,sub_zero] using (hn (D n) hDn).1

theorem dense_scaled_path_error_tendsto (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ᶠ n in atTop, DenseStochastic (D n)) :
    Tendsto (fun n : ℕ => ((n : ℝ)^n/(n.factorial : ℝ))*(WeightedCycle.path (D n)/n)-
      (1-denseBaseKernel (D n)).det*gramGaussian (denseBaseKernel (D n))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [dense_scaled_cycle_path_errors_uniform_tendsto ε hε,hD] with n hn hDn
  simpa only [Real.dist_eq,sub_zero] using (hn (D n) hDn).2

end TournamentHamiltonian
