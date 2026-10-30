module

public import TournamentHamiltonian.PaperEndpointsA.Permanent31
public import TournamentHamiltonian.PaperEndpointsA.Activity32

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PaperEndpointsA
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

/-- C=0 and q=0 are legal, not excluded by hidden strict positivity. -/
theorem zero_uniform_constant : ∃ K : ℝ, 0≤K ∧ ∀ (ι : Type) [Fintype ι],
    0<Fintype.card ι → ∀ E : Matrix ι ι ℝ, DoublyCentered E →
      (∀ i j, |E i j|≤0) → ‖(Fintype.card ι:ℝ)⁻¹ • E‖≤0 →
      |Matrix.permanent (fun i j => 1+E i j)/((Fintype.card ι).factorial:ℝ) -
        gramGaussian ((Fintype.card ι:ℝ)⁻¹ • E)|≤K/Fintype.card ι :=
  paper_3_1_uniform_constant 0 0 (by norm_num) (by norm_num) (by norm_num)

theorem singleton_zero_matrix_bound :
    |Matrix.permanent (fun (_i _j : Fin 1) => (1:ℝ)) /
      ((Fintype.card (Fin 1)).factorial:ℝ) - gramGaussian (0 : Matrix (Fin 1) (Fin 1) ℝ)| ≤
        uniformPermanentActivityConstant 0 0 := by
  have h := paper_3_1 (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (by constructor <;> intro i <;> simp) (by simp) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp)
  simpa [gramGaussian] using h

theorem chainBudget_one_le (C q R : ℝ) : 1≤chainBudget C q R := le_max_left _ _

theorem chainBudget_at_zero_radius (C q : ℝ) : chainBudget C q 0=1 := by
  simp [chainBudget]

theorem paper_3_2_zero_radius {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0<j) (C q : ℝ) (hC : 0≤C) (hn : 0<Fintype.card ι)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q) :
    Summable (fun k : ℕ => |actualCoreExcessCoefficient B j k| * (0:ℝ)^k) ∧
      (∑' k : ℕ, |actualCoreExcessCoefficient B j k| * (0:ℝ)^k) ≤
        ((710*(j:ℝ))/(Fintype.card ι:ℝ))^j := by
  simpa [chainBudget_at_zero_radius] using paper_3_2 B j hj C q 0 hC hn
    (by norm_num) hentry hcap (by norm_num)

/-- Both bounds apply at j=1; the literal sharper first-excess constant is retained. -/
theorem two_first_activity_bounds {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (C q R : ℝ) (hC : 0≤C) (hn : 0<Fintype.card ι) (hR : 0≤R)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q) (hgap : R*q<1) :
    (∑' k : ℕ, |actualCoreExcessCoefficient B 1 k| * R^k) ≤
      710*(chainBudget C q R)^3/(Fintype.card ι:ℝ) ∧
    (∑' k : ℕ, |actualCoreExcessCoefficient B 1 k| * R^k) ≤
      ((3/2:ℝ)*(chainBudget C q R)^2+(10/3:ℝ)*(chainBudget C q R)^3)/(Fintype.card ι:ℝ) := by
  constructor
  · simpa using (paper_3_2 B 1 (by omega) C q R hC hn hR hentry hcap hgap).2
  · exact (paper_3_2_first B C q R hC hn hR hentry hcap hgap).2

theorem q_zero_default_radii : permanentAnalyticRadius 0=3/2 ∧ permanentRecoveryRadius 0=5/4 := by
  norm_num [permanentAnalyticRadius,permanentRecoveryRadius]

/-- Precise diagnostic: the old geometric recovery budget is NOT the manuscript's
K_G. At C=q=0 the manuscript expression is zero, but this budget is 330. -/
theorem geometric_recovery_budget_at_zero :
    gaussianFactorialRecoveryBudget 0 0 (5/4) (3/2)=330 := by
  norm_num [gaussianFactorialRecoveryBudget,geometricSecondMoment]

theorem old_budget_not_le_zero : ¬gaussianFactorialRecoveryBudget 0 0 (5/4) (3/2)≤0 := by
  rw [geometric_recovery_budget_at_zero]
  norm_num

end
end PaperEndpointsA
