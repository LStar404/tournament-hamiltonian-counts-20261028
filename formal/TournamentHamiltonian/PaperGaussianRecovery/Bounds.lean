module

public import TournamentHamiltonian.PaperGaussianRecovery.GramDerivatives

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

def gammaBudget (C q t : ℝ) : ℝ := Real.exp (t^2*C^2/(2*(1-t^2*q^2)))
def uBudget (C q t : ℝ) : ℝ := t^2*C^2/(1-t^2*q^2)
def vBudget (C q t : ℝ) : ℝ := t^2*C^2*(1+t^2*q^2)/(1-t^2*q^2)^2

theorem spectral_bounds (s : ι → ℝ) (C q t : ℝ)
    (ht : 0≤t) (hq : 0≤q) (hgap : t*q<1)
    (hs0 : ∀ i,0≤s i) (hsq : ∀ i,s i≤q^2) (hss : ∑ i,s i≤C^2) :
    (∀ i,0<1-t^2*s i) ∧
    0≤spectralA s t ∧ spectralA s t≤uBudget C q t ∧
    0≤spectralB s t ∧ spectralB s t≤vBudget C q t := by
  have hg : 0<1-t^2*q^2 := by
    have := mul_nonneg ht hq
    nlinarith [sq_nonneg (t*q-1)]
  have ha0 (i : ι) : 0≤t^2*s i := mul_nonneg (sq_nonneg _) (hs0 i)
  have haq (i : ι) : t^2*s i≤t^2*q^2 := mul_le_mul_of_nonneg_left (hsq i) (sq_nonneg _)
  have hp (i : ι) : 0<1-t^2*s i := lt_of_lt_of_le hg (by linarith [haq i])
  have hAi (i : ι) : t^2*s i/(1-t^2*s i)≤t^2*s i/(1-t^2*q^2) :=
    div_le_div_of_nonneg_left (ha0 i) hg (by linarith [haq i])
  have hBi (i : ι) : t^2*s i*(1+t^2*s i)/(1-t^2*s i)^2 ≤
      t^2*s i*(1+t^2*q^2)/(1-t^2*q^2)^2 := by
    apply div_le_div₀ (mul_nonneg (ha0 i) (by positivity)) (by
      exact mul_le_mul_of_nonneg_left (by linarith [haq i]) (ha0 i)) (sq_pos_of_pos hg)
    exact pow_le_pow_left₀ hg.le (by linarith [haq i]) 2
  refine ⟨hp,Finset.sum_nonneg (fun i _ => div_nonneg (ha0 i) (hp i).le),?_,
    Finset.sum_nonneg (fun i _ => div_nonneg
      (mul_nonneg (ha0 i) (by linarith [ha0 i])) (sq_nonneg _)),?_⟩
  · calc
      spectralA s t ≤ ∑ i,t^2*s i/(1-t^2*q^2) := Finset.sum_le_sum (fun i _ => hAi i)
      _ = t^2*(∑ i,s i)/(1-t^2*q^2) := by rw [←Finset.sum_div,←Finset.mul_sum]
      _ ≤ uBudget C q t := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hss (sq_nonneg _)) hg.le
  · calc
      spectralB s t ≤ ∑ i,t^2*s i*(1+t^2*q^2)/(1-t^2*q^2)^2 :=
        Finset.sum_le_sum (fun i _ => hBi i)
      _ = t^2*(∑ i,s i)*(1+t^2*q^2)/(1-t^2*q^2)^2 := by
        rw [←Finset.sum_div,←Finset.sum_mul,←Finset.mul_sum]
      _ ≤ vBudget C q t := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hss (sq_nonneg _))
          (by positivity)) (sq_nonneg _)

theorem gramGaussian_le_gamma (B : Matrix ι ι ℝ) (C q t : ℝ)
    (hC : 0≤C) (hq : 0≤q) (ht : 0≤t) (hgap : t*q<1)
    (hB : ‖B‖≤q) (hF : realFrobeniusNorm B≤C) :
    gramGaussian (t • B)≤gammaBudget C q t := by
  have hBt : ‖t • B‖≤t*q := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hB ht
  have hFt : realFrobeniusNorm (t • B)≤t*C := by
    rw [realFrobeniusNorm_smul,abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hF ht
  simpa [gammaBudget,mul_pow] using gramGaussian_le_exp_frobenius_budget (t • B)
    (t*C) (t*q) (mul_nonneg ht hC) (mul_nonneg ht hq) hgap hBt hFt

theorem gramGaussian_factorial_second_bound (B : Matrix ι ι ℝ) (C q t : ℝ)
    (hC : 0≤C) (hq : 0≤q) (ht : 0≤t) (hgap : t*q<1)
    (hB : ‖B‖≤q) (hF : realFrobeniusNorm B≤C) :
    t^2*iteratedDeriv 2 (fun s : ℝ => gramGaussian (s • B)) t ≤
      gammaBudget C q t*((uBudget C q t)^2+vBudget C q t) := by
  have hs := spectral_bounds (gramEigenvalues B) C q t ht hq hgap
    (gramEigenvalues_nonneg B) (gramEigenvalues_le B q hq hB) (by
      rw [gramEigenvalues_sum]
      exact pow_le_pow_left₀ (realFrobeniusNorm_nonneg B) hF 2)
  rw [gramGaussian_factorial_second_derivative B t hs.1]
  apply mul_le_mul (gramGaussian_le_gamma B C q t hC hq ht hgap hB hF)
  · exact add_le_add (pow_le_pow_left₀ hs.2.1 hs.2.2.1 2) hs.2.2.2.2
  · exact add_nonneg (sq_nonneg _) hs.2.2.2.1
  · exact (Real.exp_pos _).le

end
end PaperGaussianRecovery
