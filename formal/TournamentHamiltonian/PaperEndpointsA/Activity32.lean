module

public import TournamentHamiltonian.ActualCoreActivity
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

set_option autoImplicit false
namespace PaperEndpointsA
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

/-- Actual weighted core coefficient series, not a proxy norm or a merely finite window. -/
theorem core_activity_summable_and_tsum (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0<j) (C q R W : ℝ)
    (hC : 0≤C) (hn : 0<Fintype.card ι) (hR : 0≤R)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q)
    (hgap : R*q<1) (hW : 1≤W)
    (hAW : C*R+C^2*R^2/(1-R*q)≤W) :
    Summable (fun k : ℕ => |actualCoreExcessCoefficient B j k| *R^k) ∧
      (∑' k : ℕ, |actualCoreExcessCoefficient B j k| *R^k) ≤
        ((710*W^3*(j:ℝ))/(Fintype.card ι:ℝ))^j := by
  have hnonneg : 0 ≤ (fun k : ℕ => |actualCoreExcessCoefficient B j k| *R^k) :=
    fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hR k)
  have hfinite (s : Finset ℕ) := actualCoreExcessCoefficient_activity_le B j hj s C q R W
    hC hn hR hentry hcap hgap hW hAW
  exact ⟨summable_of_sum_le hnonneg hfinite,Real.tsum_le_of_sum_le hnonneg hfinite⟩

/-- The sharper first-excess coefficient sum also has genuine summability. -/
theorem first_activity_summable_and_tsum (B : Matrix ι ι ℝ) (C q R W : ℝ)
    (hC : 0≤C) (hn : 0<Fintype.card ι) (hR : 0≤R)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q)
    (hgap : R*q<1) (hAW : C*R+C^2*R^2/(1-R*q)≤W) :
    Summable (fun k : ℕ => |actualCoreExcessCoefficient B 1 k| *R^k) ∧
      (∑' k : ℕ, |actualCoreExcessCoefficient B 1 k| *R^k) ≤
        ((3/2:ℝ)*W^2+(10/3:ℝ)*W^3)/(Fintype.card ι:ℝ) := by
  have hnonneg : 0 ≤ (fun k : ℕ => |actualCoreExcessCoefficient B 1 k| *R^k) :=
    fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hR k)
  have hfinite (s : Finset ℕ) := actualCoreExcessCoefficient_one_window_le B s C q R W
    hC hn hR hentry hcap hgap hAW
  exact ⟨summable_of_sum_le hnonneg hfinite,Real.tsum_le_of_sum_le hnonneg hfinite⟩

/-- The paper's W, allowing a freely chosen valid analytic radius R. -/
def chainBudget (C q R : ℝ) : ℝ := max 1 (C*R+C^2*R^2/(1-R*q))

/-- Literal Lemma 3.2 with W exactly max{1,CR+C²R²/(1−Rq)} and D=710W³. -/
theorem paper_3_2 (B : Matrix ι ι ℝ) (j : ℕ) (hj : 0<j) (C q R : ℝ)
    (hC : 0≤C) (hn : 0<Fintype.card ι) (hR : 0≤R)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q) (hgap : R*q<1) :
    Summable (fun k : ℕ => |actualCoreExcessCoefficient B j k| *R^k) ∧
      (∑' k : ℕ, |actualCoreExcessCoefficient B j k| *R^k) ≤
        ((710*(chainBudget C q R)^3*(j:ℝ))/(Fintype.card ι:ℝ))^j :=
  core_activity_summable_and_tsum B j hj C q R (chainBudget C q R)
    hC hn hR hentry hcap hgap (le_max_left _ _) (le_max_right _ _)

theorem paper_3_2_first (B : Matrix ι ι ℝ) (C q R : ℝ)
    (hC : 0≤C) (hn : 0<Fintype.card ι) (hR : 0≤R)
    (hentry : ∀ i l, |B i l|≤C/(Fintype.card ι:ℝ)) (hcap : ‖B‖≤q) (hgap : R*q<1) :
    Summable (fun k : ℕ => |actualCoreExcessCoefficient B 1 k| *R^k) ∧
      (∑' k : ℕ, |actualCoreExcessCoefficient B 1 k| *R^k) ≤
        ((3/2:ℝ)*(chainBudget C q R)^2+(10/3:ℝ)*(chainBudget C q R)^3)/(Fintype.card ι:ℝ) :=
  first_activity_summable_and_tsum B C q R (chainBudget C q R)
    hC hn hR hentry hcap hgap (le_max_right _ _)

end
end PaperEndpointsA
