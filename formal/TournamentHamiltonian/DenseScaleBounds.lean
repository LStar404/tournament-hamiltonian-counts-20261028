module

public import TournamentHamiltonian.DensePathConvergence
public import TournamentHamiltonian.GaussianFactorialRecovery

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.L2Operator
namespace TournamentHamiltonian

noncomputable def denseGaussianBound : ℝ := Real.exp ((4 : ℝ)^2/(2*(1-(4/5 : ℝ)^2)))
noncomputable def denseDeterminantBound : ℝ := ∑' k, denseTailEnvelope 3 1 k
noncomputable def denseScaledPermanentBound : ℝ := denseGaussianBound*(denseFullPermanentConstant+1)

theorem denseScaleBounds_nonneg :
    0 ≤ denseGaussianBound ∧ 0 ≤ denseDeterminantBound ∧ 0 ≤ denseScaledPermanentBound := by
  refine ⟨(Real.exp_pos _).le, tsum_nonneg (fun k => denseTailEnvelope_nonneg (by norm_num) 1 k), ?_⟩
  unfold denseScaledPermanentBound
  exact mul_nonneg (Real.exp_pos _).le (by linarith [densePermanentConstants_nonneg.1])

/-- Genuine Gram Gaussian uniformly bounded from the fixed gap and Frobenius budget. -/
theorem DenseStochastic.gramGaussian_uniform_bounds {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) :
    1 ≤ gramGaussian (denseBaseKernel D) ∧
      gramGaussian (denseBaseKernel D) ≤ denseGaussianBound := by
  refine ⟨dense_gramGaussian_one_le_of_gap _ (hD.gap.trans_lt (by norm_num)), ?_⟩
  have h := gramGaussian_le_exp_frobenius_budget (denseBaseKernel D) 4 (4/5)
    (by norm_num) (by norm_num) (by norm_num) hD.gap (hD.kernel_frobenius hn)
  exact h

/-- Uniform determinant bound obtained from the exact principal-minor main term
and dense Hadamard layers. This uses no count asymptotic or permanent input. -/
theorem DenseStochastic.centered_det_uniform_bound {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) :
    |(1-denseBaseKernel D).det| ≤ denseDeterminantBound := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [← dense_centered_eq_base, ← WeightedCycle.cycle_main_term_eq_centered_det D hD.row_sum, abs_neg]
  calc
    _ ≤ ∑ U : Finset (Fin n), (U.card : ℝ)*
        |((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det| := by
      simpa only [abs_mul, Nat.abs_cast] using Finset.abs_sum_le_sum_abs
        (fun U : Finset (Fin n) => (U.card : ℝ)*
          ((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det) Finset.univ
    _ = ∑ k ∈ Finset.range (n+1), ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (U.card : ℝ)*|((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det| := dense_sum_by_card _ _
    _ ≤ ∑ k ∈ Finset.range (n+1), denseTailEnvelope 3 1 k := by
      apply Finset.sum_le_sum
      intro k _
      apply (hD.cycle_layer_hadamard hn k).trans
      calc
        _ ≤ (k : ℝ)*3^k*subsetWeight k := mul_le_mul_of_nonneg_left
          (denseHadamardWeight_le_subsetWeight k) (by positivity)
        _ ≤ denseTailEnvelope 3 1 k := by
          unfold denseTailEnvelope
          simp only [pow_one]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k) (subsetWeight_nonneg k)]
    _ ≤ denseDeterminantBound := (denseTailEnvelope_summable (by norm_num : (0 : ℝ) ≤ 3) 1).sum_le_tsum _
      (fun k _ => denseTailEnvelope_nonneg (by norm_num) 1 k)

/-- Absolute error on the genuine factorial-normalized permanent, proved from
its relative error and the independently established uniform Gaussian bound. -/
theorem DenseStochastic.scaled_permanent_error_bound {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) :
    |((n : ℝ)^n/(n.factorial : ℝ))*D.permanent-gramGaussian (denseBaseKernel D)| ≤
      denseGaussianBound*denseFullPermanentConstant/n := by
  have hG := hD.gramGaussian_uniform_bounds hn
  have hGp : 0 < gramGaussian (denseBaseKernel D) := lt_of_lt_of_le (by norm_num) hG.1
  calc
    _ = |((((n : ℝ)^n/(n.factorial : ℝ))*D.permanent)/gramGaussian (denseBaseKernel D)-1)*
        gramGaussian (denseBaseKernel D)| := by congr 1; field_simp
    _ = |(((n : ℝ)^n/(n.factorial : ℝ))*D.permanent)/gramGaussian (denseBaseKernel D)-1| *
        gramGaussian (denseBaseKernel D) := by rw [abs_mul,abs_of_pos hGp]
    _ ≤ (denseFullPermanentConstant/(n : ℝ))*gramGaussian (denseBaseKernel D) :=
      mul_le_mul_of_nonneg_right (hD.permanent_relative hn) hGp.le
    _ ≤ (denseFullPermanentConstant/(n : ℝ))*denseGaussianBound :=
      mul_le_mul_of_nonneg_left hG.2 (div_nonneg densePermanentConstants_nonneg.1 (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The multiplier used when restoring the count scale is uniformly bounded;
we do not multiply a vanishing error by an arbitrary varying sequence. -/
theorem DenseStochastic.scaled_permanent_uniform_bound {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) :
    |((n : ℝ)^n/(n.factorial : ℝ))*D.permanent| ≤ denseScaledPermanentBound := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAD := densePermanentConstants_nonneg.1
  have hG := hD.gramGaussian_uniform_bounds hn
  calc
    _ = |(((n : ℝ)^n/(n.factorial : ℝ))*D.permanent-gramGaussian (denseBaseKernel D))+
        gramGaussian (denseBaseKernel D)| := by congr 1; ring
    _ ≤ |((n : ℝ)^n/(n.factorial : ℝ))*D.permanent-gramGaussian (denseBaseKernel D)|+
        |gramGaussian (denseBaseKernel D)| := abs_add_le _ _
    _ ≤ denseGaussianBound*denseFullPermanentConstant/n+denseGaussianBound := by
      apply add_le_add (hD.scaled_permanent_error_bound hn)
      rw [abs_of_nonneg (le_trans (by norm_num) hG.1)]
      exact hG.2
    _ ≤ denseScaledPermanentBound := by
      unfold denseScaledPermanentBound
      have hh := mul_le_mul_of_nonneg_left (div_le_self hAD hn1) denseScaleBounds_nonneg.1
      calc
        _ = denseGaussianBound*(denseFullPermanentConstant/n)+denseGaussianBound := by ring
        _ ≤ denseGaussianBound*denseFullPermanentConstant+denseGaussianBound := add_le_add hh le_rfl
        _ = _ := by ring

end TournamentHamiltonian
