module

public import TournamentHamiltonian.PaperGaussianRecovery.Recovery
public import TournamentHamiltonian.PermanentApproximationFromActivities

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

theorem finite_window_error_fine (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι)
    (M : ℕ) (C q σ R K α : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hσ : 1 < σ) (hσR : σ < R) (hRq : R * q < 1)
    (hαquarter : α≤1/4) (hαlog : α≤Real.log σ)
    (hZ : ‖B‖ ≤ q) (hF : realFrobeniusNorm B ≤ C)
    (hcore : (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤ K)
    (hsmall : ∀ k∈Finset.range (M+1),(k:ℝ)≤α*Fintype.card ι)
    (hwindow : ∀ k ∈ Finset.range (M + 1),
      2 * k ≤ Fintype.card ι ∧ (k : ℝ) / Fintype.card ι ≤ Real.log σ) :
    (∑ k ∈ Finset.range (M + 1),
      |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k -
        bilinearGaussianCoefficient B k|) ≤
      gramGaussian (R • B) * K +
        gaussianRecoveryBudget C q σ α / Fintype.card ι := by
  have hR : 0 < R := by linarith
  have hgap : R * ‖B‖ < 1 :=
    (mul_le_mul_of_nonneg_left hZ hR.le).trans_lt hRq
  have hsum := Finset.sum_le_sum (s := Finset.range (M + 1)) (fun k hk =>
    actual_normalized_coefficient_window_error_le B hp k σ R hσ hσR.le
      (hwindow k hk).1 (hwindow k hk).2)
  rw [Finset.sum_add_distrib] at hsum
  exact hsum.trans (add_le_add
    (actual_finite_gaussian_core_error_le B hB.1 hB.2 M R K hR.le hgap hcore)
    (gaussian_factorial_recovery_fine _ hp B C q σ α hC hq hσ
      ((mul_le_mul_of_nonneg_right hσR.le hq).trans_lt hRq) hαquarter hαlog hZ hF _ hsmall))


end
end PaperGaussianRecovery
