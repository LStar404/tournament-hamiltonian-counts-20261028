module

public import TournamentHamiltonian.PaperGaussianRecovery.Approximation
public import TournamentHamiltonian.ActualCoreActivity
public import TournamentHamiltonian.UniformPermanentFromActivities
public import TournamentHamiltonian.PermanentEntryFrobenius

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

def paperW (C q R : ℝ) : ℝ := max 1 (C*R+C^2*R^2/(1-R*q))
def paperD (C q R : ℝ) : ℝ := 710*(paperW C q R)^3
def paperT (C q R : ℝ) : ℝ := (3/2:ℝ)*(paperW C q R)^2+(10/3:ℝ)*(paperW C q R)^3
def paperAlpha (C q σ R : ℝ) : ℝ := min (1/4) (min (1/(16*paperD C q R)) (Real.log σ/2))

theorem paperW_pos (C q R : ℝ) : 0<paperW C q R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
theorem paperD_pos (C q R : ℝ) : 0<paperD C q R := by
  have := paperW_pos C q R
  unfold paperD
  positivity

theorem paperAlpha_guards (C q σ R : ℝ) (hσ : 1<σ) :
    0<paperAlpha C q σ R ∧ paperAlpha C q σ R≤1/4 ∧
    16*paperD C q R*paperAlpha C q σ R≤1 ∧
    paperAlpha C q σ R≤Real.log σ := by
  have hD := paperD_pos C q R
  have hl := Real.log_pos hσ
  have hp : 0<paperAlpha C q σ R := by unfold paperAlpha; positivity
  have hq : paperAlpha C q σ R≤1/4 := min_le_left _ _
  have hd : paperAlpha C q σ R≤1/(16*paperD C q R) := (min_le_right _ _).trans (min_le_left _ _)
  have hs : paperAlpha C q σ R≤Real.log σ/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hp,hq,?_,by linarith⟩
  have hm := mul_le_mul_of_nonneg_left hd (show 0≤16*paperD C q R by positivity)
  have he : (16*paperD C q R)*(1/(16*paperD C q R))=1 := by field_simp
  rwa [he] at hm

/-- The displayed Proposition 3.5 budget, with literal Γ, K_G, D, T₁ and α. -/
def paperBudget (n : ℕ) (C q σ R : ℝ) : ℝ :=
  (gammaBudget C q R*paperT C q R+gaussianRecoveryBudget C q σ (paperAlpha C q σ R))/n +
  8*gammaBudget C q R*(paperD C q R)^2/(n:ℝ)^2 +
  R/(R-1)*Real.exp (R*C/(1-R*q)*Real.sqrt n-paperAlpha C q σ R*n*Real.log R) +
  σ*gammaBudget C q σ*Real.exp (-paperAlpha C q σ R*n*Real.log σ)

/-- No core-activity or Gaussian-moment premise remains.  The finite window is
obtained from the actual matrix coefficient theorems; K_G uses the actual
Gaussian factorial-second moment proved above. -/
theorem paper_3_5_normalized (B : Matrix ι ι ℝ) (hB : DoublyCentered B)
    (C q σ R : ℝ) (hC : 0≤C) (hq : 0≤q) (hσ : 1<σ) (hσR : σ<R) (hRq : R*q<1)
    (hn : 4/paperAlpha C q σ R≤(Fintype.card ι:ℝ))
    (hentry : ∀ i j, |B i j|≤C/Fintype.card ι) (hZ : ‖B‖≤q) :
    |Matrix.permanent (fun i j => 1+(Fintype.card ι:ℝ)*B i j)/((Fintype.card ι).factorial:ℝ)
      -gramGaussian B|≤paperBudget (Fintype.card ι) C q σ R := by
  have ha := paperAlpha_guards C q σ R hσ
  have hpR : (0:ℝ)<Fintype.card ι := (div_pos (by norm_num) ha.1).trans_le hn
  have hp : 0<Fintype.card ι := Nat.cast_pos.mp hpR
  have hR : 0≤R := by linarith
  have hW : 1≤paperW C q R := le_max_left _ _
  have hAW : C*R+C^2*R^2/(1-R*q)≤paperW C q R := le_max_right _ _
  have hF := realFrobeniusNorm_le_entry_budget B hp C hC hentry
  have hfirst := actualCoreExcessCoefficient_one_window_le B
    (Finset.range (Nat.floor (paperAlpha C q σ R*Fintype.card ι)+1)) C q R (paperW C q R)
    hC hp hR hentry hZ hRq hAW
  have hexcess (j : ℕ) (hj : j∈Finset.Icc 2 (Nat.floor (paperAlpha C q σ R*Fintype.card ι))) :
      (∑ k∈Finset.range (Nat.floor (paperAlpha C q σ R*Fintype.card ι)+1),
        |actualCoreExcessCoefficient B j k| *R^k)≤excessWindowTerm (paperD C q R) (Fintype.card ι) j := by
    have hj0 : 0<j := by have := (Finset.mem_Icc.mp hj).1; omega
    simpa only [paperD,excessWindowTerm] using actualCoreExcessCoefficient_activity_le B j hj0
      (Finset.range (Nat.floor (paperAlpha C q σ R*Fintype.card ι)+1)) C q R (paperW C q R)
      hC hp hR hentry hZ hRq hW hAW
  have h := sharp_permanent_approximation_of_core_activities B hB hp C q σ R
    (paperD C q R) (paperT C q R) (paperAlpha C q σ R) hC hq hσ hσR hRq hZ hF
    (paperD_pos C q R).le (by unfold paperT; positivity) ha.1.le ha.2.1 ha.2.2.1 ha.2.2.2 hfirst hexcess
  apply h.trans
  have heR : Real.exp ((R*C)^2/(2*(1-(R*q)^2)))=gammaBudget C q R := by simp [gammaBudget,mul_pow]
  have heσ : Real.exp ((σ*C)^2/(2*(1-(σ*q)^2))-paperAlpha C q σ R*Fintype.card ι*Real.log σ)=
      gammaBudget C q σ*Real.exp (-paperAlpha C q σ R*Fintype.card ι*Real.log σ) := by
    rw [sub_eq_add_neg,Real.exp_add]
    simp [gammaBudget,mul_pow,neg_mul]
  unfold sharpApproximationBudget paperBudget
  rw [heR,heσ]
  have ht : gammaBudget C q σ*Real.exp (-paperAlpha C q σ R*Fintype.card ι*Real.log σ)≤
      σ*gammaBudget C q σ*Real.exp (-paperAlpha C q σ R*Fintype.card ι*Real.log σ) := by
    have hx : 0≤gammaBudget C q σ*Real.exp (-paperAlpha C q σ R*Fintype.card ι*Real.log σ) := by
      unfold gammaBudget; positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hσ.le) hx]
  convert add_le_add_left ht (gammaBudget C q R * (paperT C q R / (Fintype.card ι:ℝ) +
    8*(paperD C q R)^2/(Fintype.card ι:ℝ)^2) +
    gaussianRecoveryBudget C q σ (paperAlpha C q σ R)/(Fintype.card ι:ℝ) +
    R/(R-1)*Real.exp (R*C/(1-R*q)*Real.sqrt (Fintype.card ι)-paperAlpha C q σ R*Fintype.card ι*Real.log R)) using 1 <;> ring

/-- Proposition 3.5 in the paper's original E normalization B=E/n. -/
theorem paper_3_5 (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (C q σ R : ℝ) (hC : 0≤C) (hq : 0≤q) (hσ : 1<σ) (hσR : σ<R) (hRq : R*q<1)
    (hn : 4/paperAlpha C q σ R≤(Fintype.card ι:ℝ))
    (hentry : ∀ i j, |E i j|≤C) (hZ : ‖(Fintype.card ι:ℝ)⁻¹ • E‖≤q) :
    |Matrix.permanent (fun i j => 1+E i j)/((Fintype.card ι).factorial:ℝ)
      -gramGaussian ((Fintype.card ι:ℝ)⁻¹ • E)|≤paperBudget (Fintype.card ι) C q σ R := by
  have ha := (paperAlpha_guards C q σ R hσ).1
  have hpR : (0:ℝ)<Fintype.card ι := (div_pos (by norm_num) ha).trans_le hn
  have he : ∀ i j, |((Fintype.card ι:ℝ)⁻¹ • E) i j|≤C/Fintype.card ι := by
    intro i j
    simpa [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hpR,div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_left (hentry i j) (inv_nonneg.mpr hpR.le)
  have h := paper_3_5_normalized ((Fintype.card ι:ℝ)⁻¹ • E)
    (DoublyCentered.real_smul E hE _) C q σ R hC hq hσ hσR hRq hn he hZ
  simpa only [Matrix.smul_apply,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ hpR.ne',one_mul] using h

end
end PaperGaussianRecovery
