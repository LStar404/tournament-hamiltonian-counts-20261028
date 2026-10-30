module

public import TournamentHamiltonian.DenseHadamardLayers
public import TournamentHamiltonian.DenseErrorBudget
public import TournamentHamiltonian.WeightedCycle.Integration

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology
namespace TournamentHamiltonian

/-- Exact finite regrouping by deletion size; no probability or limit argument. -/
theorem dense_sum_by_card (n : ℕ) (f : Finset (Fin n) → ℝ) :
    (∑ U : Finset (Fin n), f U) =
      ∑ k ∈ Finset.range (n+1), ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f U := by
  classical
  symm
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Finset (Fin n)))) (t := Finset.range (n+1))
    (g := Finset.card) (fun U _ => by
      simp only [Finset.mem_range, Nat.lt_succ_iff]
      simpa using U.card_le_univ) f
  simpa only [Finset.powersetCard_eq_filter, Finset.powerset_univ] using h

/-- Actual cycle count error is bounded by the explicit numerical budget. -/
theorem DenseStochastic.cycle_error_le_budget {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ)) :
    |(n : ℝ)*WeightedCycle.cyc D/D.permanent-(1-WeightedCycle.centered D).det| ≤
      ∑ k ∈ Finset.range (n+1), denseCountWeight k*denseRatioErrorBudget n k := by
  let : NeZero n := ⟨hn.ne'⟩
  have h := WeightedCycle.abs_normalized_cycle_error_le D hD.row_sum
  simp only [Fintype.card_fin] at h
  apply h.trans
  rw [dense_sum_by_card]
  apply Finset.sum_le_sum
  intro k _
  calc
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (U.card : ℝ)*|((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det| *
          denseRatioErrorBudget n k := by
      apply Finset.sum_le_sum
      intro U hU
      have hc := (Finset.mem_powersetCard.mp hU).2
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [hc, densePrincipalMinor] using hD.minor_error_le_budget hn hlarge U
    _ = (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (U.card : ℝ)*|((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det|)*
          denseRatioErrorBudget n k := by rw [Finset.sum_mul]
    _ ≤ ((k : ℝ)*3^k*denseHadamardWeight k)*denseRatioErrorBudget n k :=
      mul_le_mul_of_nonneg_right (hD.cycle_layer_hadamard hn k) (denseRatioErrorBudget_nonneg n k)
    _ ≤ denseCountWeight k*denseRatioErrorBudget n k := by
      apply mul_le_mul_of_nonneg_right _ (denseRatioErrorBudget_nonneg n k)
      unfold denseCountWeight
      have hw := denseHadamardWeight_nonneg k
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k,
        mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k) hw]

/-- Uniform over the entire actual dense matrix class; the main determinant may
vary with n and need not have a limit. No target count error is assumed. -/
theorem dense_cycle_error_uniform_tendsto :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        |(n : ℝ)*WeightedCycle.cyc D/D.permanent-(1-WeightedCycle.centered D).det| < ε := by
  intro ε hε
  have he := (Metric.tendsto_nhds.mp dense_count_budget_sum_tendsto) ε hε
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  filter_upwards [he, eventually_ge_atTop (max 1 N)] with n hn hnN
  intro D hD
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right _ _).trans hnN)
  have hb := hD.cycle_error_le_budget (by omega) (hN.trans hNn)
  exact hb.trans_lt ((le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn))

/-- Sequence form of the uniform theorem, requiring only eventual dense-class
membership, not convergence of its matrix determinant main term. -/
theorem dense_cycle_error_tendsto (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ᶠ n in atTop, DenseStochastic (D n)) :
    Tendsto (fun n : ℕ => (n : ℝ)*WeightedCycle.cyc (D n)/(D n).permanent-
      (1-WeightedCycle.centered (D n)).det) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [dense_cycle_error_uniform_tendsto ε hε,hD] with n hn hDn
  simpa only [Real.dist_eq, sub_zero] using hn (D n) hDn

end TournamentHamiltonian
