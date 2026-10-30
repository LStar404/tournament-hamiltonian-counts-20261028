module

public import TournamentHamiltonian.FixedDeletion.Convolution
public import TournamentHamiltonian.FixedDeletion.HitLayers

@[expose] public section

set_option autoImplicit false
namespace FixedDeletion
open TournamentHamiltonian Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem ratio_difference_bound {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U V : Finset (Fin n)) (hdis : Disjoint U V) :
    |minorRatio D (U∪V)-minorRatio D V| ≤
      denseRatioErrorBudget n (V.card+U.card)+denseRatioErrorBudget n V.card := by
  have hu := hD.minor_error_le_budget hn hlarge (U∪V)
  have hv := hD.minor_error_le_budget hn hlarge V
  have hc : (U∪V).card = V.card+U.card := by rw [Finset.card_union_of_disjoint hdis]; omega
  change |minorRatio D (U∪V)-1| ≤ _ at hu
  change |minorRatio D V-1| ≤ _ at hv
  rw [hc] at hu
  calc
    _ = |(minorRatio D (U∪V)-1)-(minorRatio D V-1)| := by congr 1; ring
    _ ≤ |minorRatio D (U∪V)-1|+|minorRatio D V-1| := abs_sub _ _
    _ ≤ _ := add_le_add hu hv

theorem ratio_absolute_bound {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (V : Finset (Fin n)) :
    |minorRatio D V| ≤ denseGlobalRatioPrefactor*denseGlobalRatioBase^V.card := by
  obtain ⟨_, h0, h⟩ := hD.minor_ratio_le_geometric hn hlarge V
  exact (abs_of_nonneg h0).trans_le h

theorem difference_layer_bound {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) (f : Finset (Fin n) → ℝ) (j : ℕ)
    (hfull : (∑ V ∈ layer n j, |f V|) ≤ denseCountWeight j)
    (hhit : (∑ V ∈ hitLayer U j, |f V|) ≤ ((U.card : ℝ)*j/n)*denseCountWeight j) :
    (∑ V ∈ layer n j, |if Disjoint U V then
        f V*(minorRatio D (U∪V)-minorRatio D V) else -f V*minorRatio D V|) ≤
      denseCountWeight j*(denseRatioErrorBudget n (j+U.card)+denseRatioErrorBudget n j)+
        ((U.card : ℝ)/n)*((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j) := by
  let e := denseRatioErrorBudget n (j+U.card)+denseRatioErrorBudget n j
  let c := denseGlobalRatioPrefactor*denseGlobalRatioBase^j
  have he : 0 ≤ e := add_nonneg (denseRatioErrorBudget_nonneg _ _) (denseRatioErrorBudget_nonneg _ _)
  have hc : 0 ≤ c := by
    have := denseGlobalRatioPrefactor_one_le
    have := denseGlobalRatioBase_one_le
    dsimp [c]; positivity
  calc
    _ ≤ ∑ V ∈ layer n j, (|f V| *e + if ¬ Disjoint U V then |f V| *c else 0) := by
      apply Finset.sum_le_sum
      intro V hV
      have hj : V.card = j := (Finset.mem_powersetCard.mp hV).2
      by_cases hd : Disjoint U V
      · simp only [hd, ite_true, not_true_eq_false, ite_false, add_zero, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa only [hj] using ratio_difference_bound hD hn hlarge U V hd
      · simp only [hd, ite_false, not_false_eq_true, ite_true, abs_mul, abs_neg]
        have hr : |minorRatio D V| ≤ c := by simpa only [hj] using ratio_absolute_bound hD hn hlarge V
        have hb := mul_le_mul_of_nonneg_left hr (abs_nonneg (f V))
        exact hb.trans (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) he))
    _ = (∑ V ∈ layer n j, |f V|)*e + (∑ V ∈ hitLayer U j, |f V|)*c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_mul]
      rfl
    _ ≤ denseCountWeight j*e + (((U.card : ℝ)*j/n)*denseCountWeight j)*c :=
      add_le_add (mul_le_mul_of_nonneg_right hfull he) (mul_le_mul_of_nonneg_right hhit hc)
    _ = _ := by dsimp [e,c]; ring

/-- One shared quantitative bound for any genuine convolution coefficient with
the proved full and fixed-hit Hadamard layers. -/
theorem difference_le_budget {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) (f : Finset (Fin n) → ℝ)
    (hfull : ∀ j, (∑ V ∈ layer n j, |f V|) ≤ denseCountWeight j)
    (hhit : ∀ j, (∑ V ∈ hitLayer U j, |f V|) ≤ ((U.card : ℝ)*j/n)*denseCountWeight j) :
    |difference D U f| ≤ budget U.card n := by
  unfold difference
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [dense_sum_by_card]
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1),
        (denseCountWeight j*(denseRatioErrorBudget n (j+U.card)+denseRatioErrorBudget n j)+
          ((U.card : ℝ)/n)*((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j)) := by
      apply Finset.sum_le_sum
      intro j _
      exact difference_layer_bound hD hn hlarge U f j (hfull j) (hhit j)
    _ = budget U.card n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl

theorem cycle_full_layer {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (j : ℕ) :
    (∑ V ∈ layer n j, |cycleCoeff D V|) ≤ denseCountWeight j := by
  have h := hD.cycle_layer_hadamard hn j
  simp only [cycleCoeff, abs_mul, abs_neg, Nat.abs_cast]
  apply h.trans
  unfold denseCountWeight
  have hw := denseHadamardWeight_nonneg j
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j,
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j) hw]

theorem path_full_layer {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (j : ℕ) :
    (∑ V ∈ layer n j, |pathCoeff D V/(n : ℝ)|) ≤ denseCountWeight j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [pathCoeff, abs_div, abs_of_pos hnR, Finset.sum_div, layer, denseCountWeight] using hD.path_layer_hadamard hn j

/-- Actual cycle deletion stability on the original permanent scale. No retained
matrix is required or asserted to be doubly stochastic. -/
theorem cycle_deletion_le_budget {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) :
    |(((n-U.card : ℕ) : ℝ)*WeightedCycle.cyc (densePrincipalMinor D U)-
      (n : ℝ)*WeightedCycle.cyc D)/D.permanent| ≤ budget U.card n := by
  have h := difference_le_budget hD hn hlarge U (cycleCoeff D)
    (cycle_full_layer hD hn) (cycle_hit_layer hD hn U)
  rw [← cycle_difference_eq] at h
  simpa only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, principal_fin] using h

/-- Actual path deletion stability with its essential ambient 1/n prefactor. -/
theorem path_deletion_le_budget {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) :
    |(WeightedCycle.path (densePrincipalMinor D U)-WeightedCycle.path D)/((n : ℝ)*D.permanent)| ≤ budget U.card n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := difference_le_budget hD hn hlarge U (fun V => pathCoeff D V/(n : ℝ))
    (path_full_layer hD hn) (fun j => by
      simpa only [abs_div, abs_of_pos hnR] using path_hit_layer hD hn U j)
  have he := path_difference_eq D U
  simp only [Fintype.card_fin] at he
  rw [← he] at h
  simpa only [Fintype.card_fin, principal_fin] using h

/-- A fixed deletion size is chosen before the epsilon cutoff, which precedes
all matrices and all deletion sets. The old count objects occur literally. -/
theorem deletion_errors_uniform_tendsto (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        ∀ U : Finset (Fin n), U.card = k →
          |(((n-k : ℕ) : ℝ)*WeightedCycle.cyc (densePrincipalMinor D U)-
            (n : ℝ)*WeightedCycle.cyc D)/D.permanent| < ε ∧
          |(WeightedCycle.path (densePrincipalMinor D U)-WeightedCycle.path D)/((n : ℝ)*D.permanent)| < ε := by
  intro ε hε
  have he := (Metric.tendsto_nhds.mp (budget_tendsto k)) ε hε
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  filter_upwards [he,eventually_ge_atTop (max 1 N)] with n hn hnN
  intro D hD U hU
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right _ _).trans hnN)
  have hb : budget k n < ε := (le_abs_self _).trans_lt (by simpa only [Real.dist_eq,sub_zero] using hn)
  have hc := cycle_deletion_le_budget hD (by omega) (hN.trans hNn) U
  have hp := path_deletion_le_budget hD (by omega) (hN.trans hNn) U
  rw [hU] at hc hp
  exact ⟨hc.trans_lt hb,hp.trans_lt hb⟩

end
end FixedDeletion
