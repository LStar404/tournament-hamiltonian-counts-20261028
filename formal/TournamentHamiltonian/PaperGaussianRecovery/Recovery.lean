module

public import TournamentHamiltonian.PaperGaussianRecovery.Bounds
public import TournamentHamiltonian.PaperGaussianRecovery.Series
public import TournamentHamiltonian.PaperGaussianRecovery.Factorial

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def gaussianRecoveryBudget (C q σ α : ℝ) : ℝ :=
  gammaBudget C q σ/(2*(1-α))*((uBudget C q σ)^2+vBudget C q σ)

theorem factorial_second_summable_bound (B : Matrix ι ι ℝ) (C q t : ℝ)
    (hC : 0≤C) (hq : 0≤q) (ht : 0≤t) (hgap : t*q<1)
    (hB : ‖B‖≤q) (hF : realFrobeniusNorm B≤C) :
    Summable (fun k : ℕ => (k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*t^k) ∧
    (∑' k : ℕ,(k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*t^k) ≤
      gammaBudget C q t*((uBudget C q t)^2+vBudget C q t) := by
  have hgap' : |t| *‖B‖<1 := by
    rw [abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left hB ht).trans_lt hgap
  have hs := factorial_second_hasSum B t hgap'
  exact ⟨hs.summable, hs.tsum_eq.trans_le
    (gramGaussian_factorial_second_bound B C q t hC hq ht hgap hB hF)⟩

theorem factorial_weight_nonneg (B : Matrix ι ι ℝ) (t : ℝ) (ht : 0≤t) (k : ℕ) :
    0≤(k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*t^k := by
  rcases k with _|k
  · simp
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k])) (bilinearGaussianCoefficient_nonneg B _)) (pow_nonneg ht _)

theorem gaussian_factorial_recovery_fine (n : ℕ) (hn : 0<n) (B : Matrix ι ι ℝ)
    (C q σ α : ℝ) (hC : 0≤C) (hq : 0≤q) (hσ : 1<σ) (hσq : σ*q<1)
    (hα : α≤1/4) (hαlog : α≤Real.log σ)
    (hB : ‖B‖≤q) (hF : realFrobeniusNorm B≤C) (s : Finset ℕ)
    (hwindow : ∀ k∈s,(k:ℝ)≤α*n) :
    (∑ k∈s,(factorialRecoveryRatio n k-1)*bilinearGaussianCoefficient B k) ≤
      gaussianRecoveryBudget C q σ α/n := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hden : 0<2*(1-α) := by linarith
  have hσ0 : 0≤σ := by linarith
  have hm := factorial_second_summable_bound B C q σ hC hq hσ0 hσq hB hF
  have hfinite := hm.1.sum_le_tsum s (fun k _ => factorial_weight_nonneg B σ hσ0 k)
  have hpoint (k : ℕ) (hk : k∈s) :
      (factorialRecoveryRatio n k-1)*bilinearGaussianCoefficient B k ≤
      ((k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*σ^k)/(2*(1-α)*n) := by
    have h := (factorialRecoveryRatio_sub_one_fine n k hn α σ hα hσ hαlog (hwindow k hk)).2
    exact (mul_le_mul_of_nonneg_right h (bilinearGaussianCoefficient_nonneg B k)).trans_eq (by ring)
  calc
    _ ≤ ∑ k∈s,((k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*σ^k)/(2*(1-α)*n) :=
      Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = (∑ k∈s,(k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*σ^k)/(2*(1-α)*n) := by rw [Finset.sum_div]
    _ ≤ (gammaBudget C q σ*((uBudget C q σ)^2+vBudget C q σ))/(2*(1-α)*n) :=
      div_le_div_of_nonneg_right (hfinite.trans hm.2) (mul_nonneg hden.le hnR.le)
    _ = gaussianRecoveryBudget C q σ α/n := by
      unfold gaussianRecoveryBudget
      field_simp [hden.ne',hnR.ne']

end
end PaperGaussianRecovery
