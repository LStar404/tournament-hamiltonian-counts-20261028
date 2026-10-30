module

public import TournamentHamiltonian.DenseGlobalRatio
public import TournamentHamiltonian.DenseTailKernel

set_option autoImplicit false

@[expose] public section
open Filter
open scoped Topology
namespace TournamentHamiltonian

/-- A log bound on a positive real ratio controls its actual additive error. -/
theorem dense_abs_sub_one_le_exp (r x : ℝ) (hr : 0 < r)
    (h : |Real.log r| ≤ x) : |r-1| ≤ Real.exp x-1 := by
  have hu : r ≤ Real.exp x := by
    rw [← Real.exp_log hr]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans h)
  have hl : Real.exp (-x) ≤ r := by
    rw [← Real.exp_log hr]
    exact Real.exp_le_exp.mpr (abs_le.mp h).1
  apply abs_le.mpr
  constructor
  · linarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]
  · linarith

/-- Explicit ambient/deletion error budget: a summable geometric cap everywhere,
and the actual small-deletion logarithmic error whenever that estimate applies. -/
noncomputable def denseRatioErrorBudget (n k : ℕ) : ℝ :=
  if (k : ℝ) ≤ denseMinorDeletionThreshold*n then
    min ((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k)
      (Real.exp (denseMinorRatioConstant*((k : ℝ)+1)^2/n)-1)
  else (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k

theorem denseRatioErrorBudget_nonneg (n k : ℕ) : 0 ≤ denseRatioErrorBudget n k := by
  have hc : 0 ≤ (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k := by
    have := denseGlobalRatioPrefactor_one_le
    have := denseGlobalRatioBase_one_le
    positivity
  have he : 0 ≤ Real.exp (denseMinorRatioConstant*((k : ℝ)+1)^2/n)-1 := by
    have harg : 0 ≤ denseMinorRatioConstant*((k : ℝ)+1)^2/n := by
      have := denseMinorRatioConstant_pos
      positivity
    linarith [Real.one_le_exp_iff.mpr harg]
  unfold denseRatioErrorBudget
  split_ifs
  · exact le_min hc he
  · exact hc

theorem denseRatioErrorBudget_le_cap (n k : ℕ) :
    denseRatioErrorBudget n k ≤ (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k := by
  unfold denseRatioErrorBudget
  split_ifs
  · exact min_le_left _ _
  · rfl

/-- The envelope controls the actual permanent ratio error for every U. -/
theorem DenseStochastic.minor_error_le_budget {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) :
    |(densePrincipalMinor D U).permanent/D.permanent-1| ≤ denseRatioErrorBudget n U.card := by
  obtain ⟨hDp,hr0,hr⟩ := hD.minor_ratio_le_geometric hn hlarge U
  have hpow : 1 ≤ denseGlobalRatioBase^U.card := one_le_pow₀ denseGlobalRatioBase_one_le
  have hcap : |(densePrincipalMinor D U).permanent/D.permanent-1| ≤
      (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^U.card := by
    have hh := abs_sub ((densePrincipalMinor D U).permanent/D.permanent) 1
    rw [abs_of_nonneg hr0, abs_one] at hh
    nlinarith
  unfold denseRatioErrorBudget
  split_ifs with hk
  · apply le_min hcap
    obtain ⟨_,hQp,hlog⟩ := hD.minor_permanent_log_bound hn hlarge U hk
    exact dense_abs_sub_one_le_exp _ _ (div_pos hQp hDp) hlog
  · exact hcap

/-- For each fixed deletion size the actual scalar budget tends to zero. -/
theorem denseRatioErrorBudget_tendsto (k : ℕ) :
    Tendsto (fun n => denseRatioErrorBudget n k) atTop (𝓝 0) := by
  have hδ := denseMinorDeletionThreshold_pos
  have hquot : Tendsto (fun n : ℕ => denseMinorRatioConstant*((k : ℝ)+1)^2/(n : ℝ))
      atTop (𝓝 0) := tendsto_natCast_atTop_atTop.const_div_atTop _
  have he : Tendsto (fun n : ℕ => Real.exp (denseMinorRatioConstant*((k : ℝ)+1)^2/n)-1)
      atTop (𝓝 0) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp hquot).sub_const 1
  have hc : 0 ≤ (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k := by
    have := denseGlobalRatioPrefactor_one_le
    have := denseGlobalRatioBase_one_le
    positivity
  have hm := (tendsto_const_nhds (x := (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k)).min he
  have hm' : Tendsto (fun n : ℕ => min ((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k)
      (Real.exp (denseMinorRatioConstant*((k : ℝ)+1)^2/n)-1)) atTop (𝓝 0) := by
    simpa only [min_eq_right hc] using hm
  apply hm'.congr'
  obtain ⟨N,hN⟩ := exists_nat_ge ((k : ℝ)/denseMinorDeletionThreshold)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (k : ℝ) ≤ denseMinorDeletionThreshold*n := by
    have hh := (div_le_iff₀ hδ).mp (hN.trans hNn)
    nlinarith
  simp [denseRatioErrorBudget, hk]

/-- One common weight for cycles and paths, including k=0. -/
noncomputable def denseCountWeight (k : ℕ) : ℝ :=
  (1+(k : ℝ))*3^k*denseHadamardWeight k

theorem denseCountWeight_nonneg (k : ℕ) : 0 ≤ denseCountWeight k := by
  unfold denseCountWeight
  exact mul_nonneg (by positivity) (denseHadamardWeight_nonneg k)

/-- The same explicit summable majorant handles the true finite coefficients. -/
theorem dense_count_budget_le_envelope (n k : ℕ) :
    denseCountWeight k*denseRatioErrorBudget n k ≤
      (denseGlobalRatioPrefactor+1)*denseTailEnvelope (3*denseGlobalRatioBase) 1 k := by
  have hC : 0 ≤ denseGlobalRatioPrefactor+1 := by linarith [denseGlobalRatioPrefactor_one_le]
  have ha : 0 ≤ denseGlobalRatioBase := le_trans (by norm_num) denseGlobalRatioBase_one_le
  calc
    _ ≤ denseCountWeight k*((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k) :=
      mul_le_mul_of_nonneg_left (denseRatioErrorBudget_le_cap n k) (denseCountWeight_nonneg k)
    _ ≤ ((1+(k : ℝ))*3^k*subsetWeight k)*
        ((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (denseHadamardWeight_le_subsetWeight k) (by positivity)
    _ = _ := by simp only [denseTailEnvelope, pow_one, mul_pow]; ring

/-- A fully concrete vanishing tail/head budget, with no convergence or
summability assumption left for the caller. -/
theorem dense_count_budget_sum_tendsto :
    Tendsto (fun n => ∑ k ∈ Finset.range (n+1),
      denseCountWeight k*denseRatioErrorBudget n k) atTop (𝓝 0) := by
  apply tendsto_triangular_sum_zero_of_dense_envelope
    (fun n k => denseCountWeight k*denseRatioErrorBudget n k)
    (3*denseGlobalRatioBase) (denseGlobalRatioPrefactor+1) 1 0
  · have := denseGlobalRatioBase_one_le; positivity
  · linarith [denseGlobalRatioPrefactor_one_le]
  · intro k
    simpa using (denseRatioErrorBudget_tendsto k).const_mul (denseCountWeight k)
  · intro n _ k _
    rw [abs_of_nonneg (mul_nonneg (denseCountWeight_nonneg k) (denseRatioErrorBudget_nonneg n k))]
    exact dense_count_budget_le_envelope n k

end TournamentHamiltonian
