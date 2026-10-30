module

public import TournamentHamiltonian.DenseMinorRatio
public import TournamentHamiltonian.DenseSubstochastic
public import TournamentHamiltonian.DenseTailScalars

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace TournamentHamiltonian

/-- Fixed prefactor for all deletion sizes. -/
noncomputable def denseGlobalRatioPrefactor : ℝ := 2 + Real.exp denseMinorRatioConstant

/-- Fixed exponential base: neither ambient size, matrix, nor deletion enters. -/
noncomputable def denseGlobalRatioBase : ℝ :=
  Real.exp (4*denseMinorRatioConstant*denseMinorDeletionThreshold + 1/denseMinorDeletionThreshold)

theorem denseGlobalRatioPrefactor_one_le : 1 ≤ denseGlobalRatioPrefactor := by
  unfold denseGlobalRatioPrefactor
  linarith [Real.exp_pos denseMinorRatioConstant]

theorem denseGlobalRatioBase_one_le : 1 ≤ denseGlobalRatioBase := by
  apply Real.one_le_exp_iff.mpr
  exact add_nonneg (by positivity [denseMinorRatioConstant_pos, denseMinorDeletionThreshold_pos])
    (one_div_nonneg.mpr denseMinorDeletionThreshold_pos.le)

/-- Independent all-deletion reciprocal bound. The proof uses the actual
permanent lower bound and the elementary substochastic bound, not cycle/path counts. -/
theorem DenseStochastic.minor_ratio_le_exp_ambient {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 2*denseFullPermanentConstant ≤ (n : ℝ)) (U : Finset (Fin n)) :
    0 < D.permanent ∧
      0 ≤ (densePrincipalMinor D U).permanent / D.permanent ∧
      (densePrincipalMinor D U).permanent / D.permanent ≤ 2*Real.exp n := by
  have hlow := hD.permanent_lower hn hlarge
  have hlowpos : (0 : ℝ) < (n.factorial : ℝ)/(2*(n : ℝ)^n) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hDp : 0 < D.permanent := hlowpos.trans_le hlow
  have hQ := hD.minor_permanent_le_one U
  refine ⟨hDp, div_nonneg hQ.1 hDp.le, ?_⟩
  calc
    _ ≤ 1/D.permanent := div_le_div_of_nonneg_right hQ.2 hDp.le
    _ ≤ 1/((n.factorial : ℝ)/(2*(n : ℝ)^n)) := one_div_le_one_div_of_le hlowpos hlow
    _ = 2*((n : ℝ)^n/(n.factorial : ℝ)) := by field_simp
    _ ≤ 2*Real.exp n := mul_le_mul_of_nonneg_left (dense_inverse_factorial_le_exp n) (by norm_num)

/-- Actual uniform geometric domination for every principal deletion, including
full deletion. The only size restriction is a fixed absolute ambient threshold. -/
theorem DenseStochastic.minor_ratio_le_geometric {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) :
    0 < D.permanent ∧
      0 ≤ (densePrincipalMinor D U).permanent / D.permanent ∧
      (densePrincipalMinor D U).permanent / D.permanent ≤
        denseGlobalRatioPrefactor*denseGlobalRatioBase^U.card := by
  have hδ := denseMinorDeletionThreshold_pos
  have hC := denseMinorRatioConstant_pos
  have hlarge' : 2*denseFullPermanentConstant ≤ (n : ℝ) := by
    linarith [densePermanentConstants_nonneg.1, densePermanentConstants_nonneg.2]
  obtain ⟨hDp,hr0,hrlarge⟩ := hD.minor_ratio_le_exp_ambient hn hlarge' U
  refine ⟨hDp, hr0, ?_⟩
  by_cases hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold*n
  · obtain ⟨_,hQp,hlog⟩ := hD.minor_permanent_log_bound hn hlarge U hk
    have hr := dense_ratio_le_of_log_bound _ _ _ (div_pos hQp hDp) hC.le hδ.le
      n U.card hn hk hlog
    have hb : Real.exp (4*denseMinorRatioConstant*denseMinorDeletionThreshold) ≤
        denseGlobalRatioBase := by
      apply Real.exp_le_exp.mpr
      exact le_add_of_nonneg_right (one_div_nonneg.mpr hδ.le)
    apply hr.trans
    apply mul_le_mul
    · exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    · exact pow_le_pow_left₀ (Real.exp_pos _).le hb _
    · positivity
    · exact denseGlobalRatioPrefactor_one_le.trans' (by norm_num)
  · have hk' : denseMinorDeletionThreshold*(n : ℝ) ≤ U.card := (not_le.mp hk).le
    have he := dense_exp_ambient_le_geometric _ hδ n U.card hk'
    have hb : Real.exp (1/denseMinorDeletionThreshold) ≤ denseGlobalRatioBase := by
      apply Real.exp_le_exp.mpr
      exact le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ 2*Real.exp n := hrlarge
      _ ≤ 2*(Real.exp (1/denseMinorDeletionThreshold))^U.card :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ ≤ denseGlobalRatioPrefactor*denseGlobalRatioBase^U.card := by
        apply mul_le_mul
        · exact le_add_of_nonneg_right (Real.exp_pos _).le
        · exact pow_le_pow_left₀ (Real.exp_pos _).le hb _
        · positivity
        · exact denseGlobalRatioPrefactor_one_le.trans' (by norm_num)

/-- Absolute constants and cutoff precede every matrix and every deleted subset. -/
theorem exists_dense_global_minor_ratio_bound :
    ∃ C a : ℝ, 1 ≤ C ∧ 1 ≤ a ∧ ∃ N : ℕ, 20 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ D : Matrix (Fin n) (Fin n) ℝ,
        DenseStochastic D → ∀ U : Finset (Fin n),
          0 < D.permanent ∧ 0 ≤ (densePrincipalMinor D U).permanent/D.permanent ∧
          (densePrincipalMinor D U).permanent/D.permanent ≤ C*a^U.card := by
  obtain ⟨N,hN⟩ := exists_nat_gt (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  refine ⟨denseGlobalRatioPrefactor,denseGlobalRatioBase,denseGlobalRatioPrefactor_one_le,
    denseGlobalRatioBase_one_le,max 20 N,le_max_left _ _,?_⟩
  intro n hn D hD U
  have hn20 : 20 ≤ n := (le_max_left _ _).trans hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right 20 N).trans hn)
  exact hD.minor_ratio_le_geometric (by omega) (hN.le.trans hNn) U

end TournamentHamiltonian
