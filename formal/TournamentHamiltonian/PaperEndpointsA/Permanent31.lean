module

public import TournamentHamiltonian.ActualCoreActivityPredicate
public import TournamentHamiltonian.RectangularPermanentApproximation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PaperEndpointsA
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

/-- The normalized entry bound is derived, not added as a caller premise. -/
theorem normalized_entry_bound (E : Matrix ι ι ℝ) (hn : 0<Fintype.card ι)
    (C : ℝ) (hE : ∀ i j, |E i j|≤C) :
    ∀ i j, |((Fintype.card ι : ℝ)⁻¹ • E) i j| ≤ C / Fintype.card ι := by
  intro i j
  have hp : (0:ℝ)<Fintype.card ι := by exact_mod_cast hn
  simpa [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hp,div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (hE i j) (inv_nonneg.mpr hp.le)

/-- Literal Theorem 3.1: the actual activity obligation is discharged internally
from entry/operator bounds. The same explicit constant works for every dimension. -/
theorem paper_3_1 (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (hn : 0<Fintype.card ι) (C q : ℝ) (hC : 0≤C) (hq : 0≤q) (hq1 : q<1)
    (hentry : ∀ i j, |E i j|≤C) (hcap : ‖(Fintype.card ι : ℝ)⁻¹ • E‖≤q) :
    |Matrix.permanent (fun i j => 1+E i j) / ((Fintype.card ι).factorial:ℝ) -
      gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E)| ≤
        uniformPermanentActivityConstant C q / Fintype.card ι :=
  uniform_permanent_approximation_of_activity_predicate E hE hn C q hC hq hq1 hentry hcap
    (actualCoreActivities_of_matrix_bounds _ C q hn hC hq hq1
      (normalized_entry_bound E hn C hentry) hcap)

/-- The paper writes BBᵀ; the existing Gram definition uses BᵀB. The actual
square determinant identity reconciles these, without changing the Gaussian factor. -/
theorem gramGaussian_square_form (B : Matrix ι ι ℝ) :
    gramGaussian B = (Real.sqrt ((1 : Matrix ι ι ℝ)-B*B.transpose).det)⁻¹ := by
  unfold gramGaussian
  rw [Matrix.det_one_sub_mul_comm]

/-- The displayed determinant version of (3.1), with the positive real square root. -/
theorem paper_3_1_determinant (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (hn : 0<Fintype.card ι) (C q : ℝ) (hC : 0≤C) (hq : 0≤q) (hq1 : q<1)
    (hentry : ∀ i j, |E i j|≤C) (hcap : ‖(Fintype.card ι : ℝ)⁻¹ • E‖≤q) :
    |Matrix.permanent (fun i j => 1+E i j) / ((Fintype.card ι).factorial:ℝ) -
      (Real.sqrt ((1 : Matrix ι ι ℝ) - ((Fintype.card ι : ℝ)⁻¹ • E) *
        ((Fintype.card ι : ℝ)⁻¹ • E).transpose).det)⁻¹| ≤
        uniformPermanentActivityConstant C q / Fintype.card ι := by
  rw [←gramGaussian_square_form]
  exact paper_3_1 E hE hn C q hC hq hq1 hentry hcap

/-- Literal dimension-uniform quantifier: K depends only on C,q, with no remaining
activity, coefficient-window or asymptotic hypotheses. -/
theorem paper_3_1_uniform_constant (C q : ℝ) (hC : 0≤C) (hq : 0≤q) (hq1 : q<1) :
    ∃ K : ℝ, 0≤K ∧ ∀ (ι : Type) [Fintype ι], 0<Fintype.card ι →
      ∀ E : Matrix ι ι ℝ, DoublyCentered E → (∀ i j, |E i j|≤C) →
      ‖(Fintype.card ι:ℝ)⁻¹ • E‖≤q →
      |Matrix.permanent (fun i j => 1+E i j) / ((Fintype.card ι).factorial:ℝ) -
        gramGaussian ((Fintype.card ι:ℝ)⁻¹ • E)| ≤ K/Fintype.card ι := by
  refine ⟨uniformPermanentActivityConstant C q,uniformPermanentActivityConstant_nonneg C q hq hq1,?_⟩
  intro ι _ hn E hc he hz
  exact paper_3_1 E hc hn C q hC hq hq1 he hz

/-- The relative-error form stated immediately after (3.1). -/
theorem paper_3_1_relative (E : Matrix ι ι ℝ) (hE : DoublyCentered E)
    (hn : 0<Fintype.card ι) (C q : ℝ) (hC : 0≤C) (hq : 0≤q) (hq1 : q<1)
    (hentry : ∀ i j, |E i j|≤C) (hcap : ‖(Fintype.card ι : ℝ)⁻¹ • E‖≤q) :
    |(Matrix.permanent (fun i j => 1+E i j) / ((Fintype.card ι).factorial:ℝ)) /
      gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E) - 1| ≤
        uniformPermanentActivityConstant C q / Fintype.card ι := by
  let G := gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E)
  have hg : 1≤G := gramGaussian_one_le_of_gap _ (hcap.trans_lt hq1)
  have hgp : 0<G := by linarith
  have h := paper_3_1 E hE hn C q hC hq hq1 hentry hcap
  have he (a : ℝ) : |a/G-1| = |a-G|/G := by
    rw [←div_self hgp.ne',←sub_div,abs_div,abs_of_pos hgp]
  rw [he]
  exact (div_le_self (abs_nonneg _) hg).trans h

end
end PaperEndpointsA
