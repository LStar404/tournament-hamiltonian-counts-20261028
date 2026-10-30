module

public import TournamentHamiltonian.DensePermanentInputs
public import TournamentHamiltonian.DenseRatioAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator
namespace TournamentHamiltonian

noncomputable def denseMinorRatioConstant : ℝ := 10 + 4096*denseMinorInverseBudget^2 +
  denseMinorGramConstant + 4*denseScaledPermanentConstant + 2*denseFullPermanentConstant

theorem denseMinorRatioConstant_pos : 0 < denseMinorRatioConstant := by
  unfold denseMinorRatioConstant
  nlinarith [denseMinorGramConstant_pos,densePermanentConstants_nonneg.1,
    densePermanentConstants_nonneg.2,sq_nonneg denseMinorInverseBudget]

theorem denseMinorRatioConstant_one_le : 1 ≤ denseMinorRatioConstant := by
  unfold denseMinorRatioConstant
  nlinarith [denseMinorGramConstant_pos,densePermanentConstants_nonneg.1,
    densePermanentConstants_nonneg.2,sq_nonneg denseMinorInverseBudget]

/-- Actual principal minor permanent ratio. The only size constraints are fixed
absolute small deletion and a fixed absolute lower bound on n. -/
theorem DenseStochastic.minor_permanent_log_bound {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n:ℝ))
    (U : Finset (Fin n)) (hk : (U.card:ℝ) ≤ denseMinorDeletionThreshold*n) :
    0 < D.permanent ∧ 0 < (densePrincipalMinor D U).permanent ∧
      |Real.log ((densePrincipalMinor D U).permanent / D.permanent)| ≤
        denseMinorRatioConstant * ((U.card:ℝ)+1)^2/n := by
  let M := Fintype.card (Uᶜ : Finset (Fin n))
  let H := matrixEntryMass (densePrincipalMinor D U)
  have hk16 := (dense_minor_small_proportion hn U hk).1
  have hb := hD.minor_basic hn U hk16
  have hMnat : M = n-U.card := by simp [M,Finset.card_compl]
  have hkn : U.card ≤ n := by simpa using U.card_le_univ
  have hMR : (M:ℝ) = (n:ℝ)-U.card := by rw [hMnat,Nat.cast_sub hkn]
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hMp : (0:ℝ) < M := by exact_mod_cast hb.1
  have hMh : (n:ℝ)/2 ≤ M := by rw [hMR]; linarith
  have hAD := densePermanentConstants_nonneg.1
  have hAY := densePermanentConstants_nonneg.2
  have hDe : denseFullPermanentConstant/n ≤ (1/2:ℝ) :=
    (div_le_iff₀ hnR).mpr (by linarith)
  have hYe : denseScaledPermanentConstant/M ≤ (1/2:ℝ) :=
    (div_le_iff₀ hMp).mpr (by linarith)
  obtain ⟨z,hz,hcap,hgram,hrestore⟩ := exists_dense_minor_gram_restoration D hD hn U hk
  let Y := localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z
  let GD := gramGaussian (denseBaseKernel D)
  let GY := gramGaussian (Y-averagingMatrix (Uᶜ : Finset (Fin n)))
  let rD := ((n:ℝ)^n/(n.factorial:ℝ))*D.permanent/GD
  let rY := ((M:ℝ)^M/(M.factorial:ℝ))*Y.permanent/GY
  have hGD : 0 < GD := dense_gramGaussian_pos_of_gap _ (hD.gap.trans_lt (by norm_num))
  have hGY : 0 < GY := dense_gramGaussian_pos_of_gap _ (hz.gap.trans_lt (by norm_num))
  have hrD : |rD-1| ≤ denseFullPermanentConstant/n := hD.permanent_relative hn
  have hrY : |rY-1| ≤ denseScaledPermanentConstant/M := hD.scaled_permanent_relative hn U hk16 z hz
  have hDp : 0 < D.permanent := positive_of_actual_relative_error _ _ GD _
    (by positivity) hGD (hDe.trans_lt (by norm_num)) hrD
  have hYp : 0 < Y.permanent := positive_of_actual_relative_error _ _ GY _
    (by positivity) hGY (hYe.trans_lt (by norm_num)) hrY
  have hQp : 0 < (densePrincipalMinor D U).permanent := by
    rw [hrestore]
    exact mul_pos (mul_pos (Real.exp_pos _) (pow_pos (div_pos hb.2.1 hMp) _)) hYp
  refine ⟨hDp,hQp,?_⟩
  have hlogD : |Real.log rD| ≤ 2*denseFullPermanentConstant/n := by
    simpa only [mul_div_assoc] using (dense_actual_relative_log rD _ hDe hrD).2
  have hlogY : |Real.log rY| ≤ 4*denseScaledPermanentConstant/n := by
    have hh := (dense_actual_relative_log rY _ hYe hrY).2
    apply hh.trans
    apply (le_div_iff₀ hnR).mpr
    have hmul := (div_le_div_of_nonneg_left hAY (by positivity : (0:ℝ)<(n:ℝ)/2) hMh)
    calc
      (2*(denseScaledPermanentConstant/(M:ℝ)))*(n:ℝ) ≤
        (2*(denseScaledPermanentConstant/((n:ℝ)/2)))*(n:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num)) hnR.le
      _ = _ := by field_simp; ring
  have hlogerr : |Real.log rY-Real.log rD| ≤ (4*denseScaledPermanentConstant+2*denseFullPermanentConstant)/n := by
    exact (abs_sub _ _).trans ((add_le_add hlogY hlogD).trans_eq (by ring))
  have hfac : |Real.log ((n:ℝ)^U.card*(M.factorial:ℝ)/(n.factorial:ℝ))| ≤ 2*(U.card:ℝ)^2/n := by
    rw [hMnat]
    apply dense_factorial_deletion_log _ _ hn
    have hh : 2*(U.card:ℝ) ≤ (n:ℝ) := by linarith
    exact_mod_cast hh
  have hmass := hD.minor_mass_log hn U hk16
  have hcid : |-localScalingCapacity z| ≤ 4096*denseMinorInverseBudget^2*(U.card:ℝ)^2/n := by
    rw [abs_neg,abs_of_nonneg hz.capacity_nonneg]
    exact hcap
  have hid := dense_permanent_log_identity n M U.card (by rw [hMnat]; omega) hn hb.1
    H (localScalingCapacity z) (densePrincipalMinor D U).permanent D.permanent Y.permanent GD GY
    hb.2.1 hDp hYp hGD hGY hrestore
  rw [hid]
  have htri : |-localScalingCapacity z +
      Real.log ((n:ℝ)^U.card*(M.factorial:ℝ)/(n.factorial:ℝ)) +
      (M:ℝ)*Real.log ((n:ℝ)*H/(M:ℝ)^2) + (Real.log GY-Real.log GD) +
      (Real.log rY-Real.log rD)| ≤
    |-localScalingCapacity z| + |Real.log ((n:ℝ)^U.card*(M.factorial:ℝ)/(n.factorial:ℝ))| +
      |(M:ℝ)*Real.log ((n:ℝ)*H/(M:ℝ)^2)| + |Real.log GY-Real.log GD| +
      |Real.log rY-Real.log rD| := by
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  apply htri.trans
  apply (add_le_add (add_le_add (add_le_add (add_le_add hcid hfac) hmass) hgram) hlogerr).trans
  exact dense_ratio_budget n U.card denseMinorGramConstant denseFullPermanentConstant
    denseScaledPermanentConstant denseMinorInverseBudget hnR (Nat.cast_nonneg _)
    denseMinorGramConstant_pos.le hAD hAY denseMinorInverseBudget_pos.le

/-- Absolute constants precede all matrix and deletion quantifiers. -/
theorem exists_dense_minor_permanent_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ D : Matrix (Fin n) (Fin n) ℝ, DenseStochastic D →
        ∀ U : Finset (Fin n), (U.card:ℝ) ≤ denseMinorDeletionThreshold*n →
          0 < D.permanent ∧ 0 < (densePrincipalMinor D U).permanent ∧
          |Real.log ((densePrincipalMinor D U).permanent / D.permanent)| ≤ C*((U.card:ℝ)+1)^2/n := by
  obtain ⟨N,hN⟩ := exists_nat_gt (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  refine ⟨denseMinorRatioConstant,denseMinorRatioConstant_pos,max 20 N,le_max_left _ _,?_⟩
  intro n hn D hD U hk
  have hn20 : 20 ≤ n := (le_max_left _ _).trans hn
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast ((le_max_right 20 N).trans hn)
  exact hD.minor_permanent_log_bound (by omega) (hN.le.trans hNn) U hk

end TournamentHamiltonian
