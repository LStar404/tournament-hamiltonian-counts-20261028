module

public import TournamentHamiltonian.PaperGaussianRecovery.Endpoint

@[expose] public section

set_option autoImplicit false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

/-- k=0,1 vanish: the sharp weight is k(k−1), not k². -/
theorem factorial_weight_zero_one (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ) :
    (0:ℝ)*((0:ℝ)-1)*bilinearGaussianCoefficient B 0*t^0=0 ∧
    (1:ℝ)*((1:ℝ)-1)*bilinearGaussianCoefficient B 1*t^1=0 := by norm_num

theorem recovery_ratio_zero_one (n : ℕ) (hn : 0<n) :
    factorialRecoveryRatio n 0=1 ∧ factorialRecoveryRatio n 1=1 := by
  simp [factorialRecoveryRatio, Nat.descFactorial_succ, Nat.cast_ne_zero.mpr hn.ne']

theorem zero_budgets (t α : ℝ) :
    gammaBudget 0 0 t=1 ∧ uBudget 0 0 t=0 ∧ vBudget 0 0 t=0 ∧
    gaussianRecoveryBudget 0 0 t α=0 := by
  simp [gammaBudget,uBudget,vBudget,gaussianRecoveryBudget]

theorem scalar_spectral_coefficients :
    spectralA (fun _ : Fin 1 => (1/16:ℝ)) 2=1/3 ∧
    spectralB (fun _ : Fin 1 => (1/16:ℝ)) 2=5/9 ∧
    (spectralA (fun _ : Fin 1 => (1/16:ℝ)) 2)^2+
      spectralB (fun _ : Fin 1 => (1/16:ℝ)) 2=2/3 := by
  norm_num [spectralA,spectralB,Fin.sum_univ_succ]

theorem scalar_budgets :
    uBudget (1/4) (1/4) 2=1/3 ∧ vBudget (1/4) (1/4) 2=5/9 ∧
    gammaBudget (1/4) (1/4) 2=Real.exp (1/6) := by norm_num [uBudget,vBudget,gammaBudget]

theorem empty_spectral_coefficients (t : ℝ) :
    spectralA (fun i : Fin 0 => i.elim0) t=0 ∧
    spectralB (fun i : Fin 0 => i.elim0) t=0 := by simp [spectralA,spectralB]

theorem empty_gram_gaussian (t : ℝ) :
    gramGaussian (t • (0 : Matrix (Fin 0) (Fin 0) ℝ))=1 := by simp [gramGaussian]

theorem actual_zero_factorial_moment {ι : Type*} [Fintype ι] (t : ℝ) (ht : 0≤t) :
    (∑' k : ℕ,(k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient (0 : Matrix ι ι ℝ) k*t^k)=0 := by
  have h := factorial_second_summable_bound (0 : Matrix ι ι ℝ) 0 0 t (by norm_num)
    (by norm_num) ht (by simp) (by simp) (by simp [realFrobeniusNorm])
  apply le_antisymm
  · simpa [gammaBudget,uBudget,vBudget] using h.2
  · exact tsum_nonneg (fun k => factorial_weight_nonneg _ t ht k)

theorem fine_factorial_k_two (n : ℕ) (hn : 0<n) (α σ : ℝ) (ha : α≤1/4)
    (hs : 1<σ) (hal : α≤Real.log σ) (hk : (2:ℝ)≤α*n) :
    factorialRecoveryRatio n 2-1≤σ^2/((n:ℝ)*(1-α)) := by
  have h := (factorialRecoveryRatio_sub_one_fine n 2 hn α σ ha hs hal hk).2
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hd : 0<1-α := by linarith
  convert h using 1
  norm_num
  field_simp [hnR.ne',hd.ne']

end
end PaperGaussianRecovery
