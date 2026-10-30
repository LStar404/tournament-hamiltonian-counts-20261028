module

public import TournamentHamiltonian.WeightedCycle.Core
public import TournamentHamiltonian.WeightedCycle.MainTerm

@[expose] public section

/-! Exact error decomposition for later minor-ratio analysis. Nothing in this
file asserts a limit, a spectral gap, or a permanent approximation. -/
namespace WeightedCycle
open scoped BigOperators Classical
noncomputable section

/-- Subtracting the finite main term leaves precisely the actual complementary
principal-permanent ratios minus one. Lean's totalized division allows this
algebraic identity even when the full permanent vanishes; positivity/nonzero
must be established separately before interpreting the ratios analytically. -/
theorem normalized_cycle_error {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    (Fintype.card α : ℝ) * cyc D / D.permanent - (1 - centered D).det =
      -(∑ U : Finset α, (U.card : ℝ) *
        ((-D).submatrix (Subtype.val : U → α) Subtype.val).det *
        ((D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
          D.permanent - 1)) := by
  rw [convolution, ← cycle_main_term_eq_centered_det D hrow]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, neg_div, Finset.sum_div]
  simp only [mul_div_assoc]
  ring

/-- The absolute-value form needed to apply a genuine uniform minor-ratio
bound later. There is no assumed asymptotic or hidden error estimate here. -/
theorem abs_normalized_cycle_error_le {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    |(Fintype.card α : ℝ) * cyc D / D.permanent - (1 - centered D).det| ≤
      ∑ U : Finset α, (U.card : ℝ) *
        |((-D).submatrix (Subtype.val : U → α) Subtype.val).det| *
        |(D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
          D.permanent - 1| := by
  rw [normalized_cycle_error D hrow, abs_neg]
  calc
    _ ≤ ∑ U : Finset α, |(U.card : ℝ) *
        ((-D).submatrix (Subtype.val : U → α) Subtype.val).det *
        ((D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
          D.permanent - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, Nat.abs_cast]

end
end WeightedCycle
