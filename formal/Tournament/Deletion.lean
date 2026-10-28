module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Exact deletion and restoration identities

These are the finite algebraic identities in manuscript §4.3 (equation 4.1)
and §4.4. They do not assume or prove the analytic permanent estimates,
Sinkhorn scaling, or the quantitative Hamilton-path theorem.

Row and column deletion sets are deliberately independent. The core
inclusion–exclusion theorem even permits rectangular index types.
-/

open scoped BigOperators

public section

namespace Tournament

section FiniteSums

variable {α β R : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β] [AddCommGroup R]

/-- A complement sum is the total sum minus the deleted sum. -/
theorem sum_complement_eq (I : Finset α) (f : α → R) :
    (∑ i ∈ Iᶜ, f i) = (∑ i, f i) - ∑ i ∈ I, f i := by
  exact eq_sub_of_add_eq (Finset.sum_compl_add_sum I f)

/-- Exact mass of a block after deleting arbitrary rows and columns.
This is a finite-sum inclusion–exclusion identity, with no positivity or
equal-cardinality assumptions. -/
theorem complement_block_mass (A : α → β → R) (I : Finset α) (J : Finset β) :
    (∑ i ∈ Iᶜ, ∑ j ∈ Jᶜ, A i j) =
      (∑ i, ∑ j, A i j) - (∑ i ∈ I, ∑ j, A i j) -
      (∑ i, ∑ j ∈ J, A i j) + ∑ i ∈ I, ∑ j ∈ J, A i j := by
  rw [sum_complement_eq]
  simp_rw [sum_complement_eq, Finset.sum_sub_distrib]
  abel

/-- Column-oriented form of the same identity, matching the column-error
sum in the manuscript. -/
theorem complement_block_mass_columns
    (A : α → β → R) (I : Finset α) (J : Finset β) :
    (∑ i ∈ Iᶜ, ∑ j ∈ Jᶜ, A i j) =
      (∑ i, ∑ j, A i j) - (∑ i ∈ I, ∑ j, A i j) -
      (∑ j ∈ J, ∑ i, A i j) + ∑ i ∈ I, ∑ j ∈ J, A i j := by
  rw [complement_block_mass]
  rw [Finset.sum_comm (s := Finset.univ) (t := J)]

end FiniteSums

section NormalizedMass

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- The sum of row deviations from one over the deleted rows. -/
theorem deleted_row_deviation (A : α → β → ℝ) (I : Finset α) :
    (∑ i ∈ I, ((∑ j, A i j) - 1)) =
      (∑ i ∈ I, ∑ j, A i j) - I.card := by
  simp [Finset.sum_sub_distrib]

omit [Fintype β] [DecidableEq α] [DecidableEq β] in
/-- The sum of column deviations from one over the deleted columns. -/
theorem deleted_column_deviation (A : α → β → ℝ) (J : Finset β) :
    (∑ j ∈ J, ((∑ i, A i j) - 1)) =
      (∑ j ∈ J, ∑ i, A i j) - J.card := by
  simp [Finset.sum_sub_distrib]

/-- Denominator-cleared version of manuscript equation (4.1).

`A` represents the mass-normalized matrix Ĉ, and `n / (n-t)` is the
scalar used in the retained block X. The assumptions on `n`, `t` are
explicit: the block scale is never justified by totalized division.
The equal-cardinality hypotheses do not identify the two deleted sets.
-/
theorem deletion_mass_cleared (A : α → β → ℝ) (I : Finset α) (J : Finset β)
    (n t : ℝ) (hm : n - t ≠ 0)
    (hMass : (∑ i, ∑ j, A i j) = n)
    (hI : (I.card : ℝ) = t) (hJ : (J.card : ℝ) = t) :
    (n - t) *
        (n / (n - t) * (∑ i ∈ Iᶜ, ∑ j ∈ Jᶜ, A i j) - (n - t)) =
      n * (-(∑ i ∈ I, ((∑ j, A i j) - 1)) -
        (∑ j ∈ J, ((∑ i, A i j) - 1)) +
        ∑ i ∈ I, ∑ j ∈ J, A i j) - t ^ 2 := by
  rw [complement_block_mass_columns, hMass,
    deleted_row_deviation, deleted_column_deviation, hI, hJ]
  field_simp
  ring

/-- Exact normalized deletion-mass identity, equation (4.1).
No tournament, nonnegativity, asymptotic window, or norm bound is needed. -/
theorem deletion_mass (A : α → β → ℝ) (I : Finset α) (J : Finset β)
    (n t : ℝ) (hn : n ≠ 0) (hm : n - t ≠ 0)
    (hMass : (∑ i, ∑ j, A i j) = n)
    (hI : (I.card : ℝ) = t) (hJ : (J.card : ℝ) = t) :
    n / (n - t) * (∑ i ∈ Iᶜ, ∑ j ∈ Jᶜ, A i j) - (n - t) =
      n / (n - t) *
        (-(∑ i ∈ I, ((∑ j, A i j) - 1)) -
          (∑ j ∈ J, ((∑ i, A i j) - 1)) +
          (∑ i ∈ I, ∑ j ∈ J, A i j) - t ^ 2 / n) := by
  rw [complement_block_mass_columns, hMass,
    deleted_row_deviation, deleted_column_deviation, hI, hJ]
  field_simp
  ring

omit [Fintype α] [DecidableEq α] in
/-- Exact retained-row marginal identity used immediately after (4.1).
It holds for every row, hence in particular for each retained row. -/
theorem deletion_row_marginal (A : α → β → ℝ) (J : Finset β)
    (i : α) (n t : ℝ) (hn : n ≠ 0) (hm : n - t ≠ 0) :
    n / (n - t) * (∑ j ∈ Jᶜ, A i j) - 1 =
      n / (n - t) *
        (((∑ j, A i j) - 1) + t / n - ∑ j ∈ J, A i j) := by
  rw [sum_complement_eq]
  field_simp
  ring

omit [Fintype β] [DecidableEq β] in
/-- The column marginal formula is independent of the row formula. -/
theorem deletion_column_marginal (A : α → β → ℝ) (I : Finset α)
    (j : β) (n t : ℝ) (hn : n ≠ 0) (hm : n - t ≠ 0) :
    n / (n - t) * (∑ i ∈ Iᶜ, A i j) - 1 =
      n / (n - t) *
        (((∑ i, A i j) - 1) + t / n - ∑ i ∈ I, A i j) := by
  exact deletion_row_marginal (fun j i => A i j) I j n t hn hm

end NormalizedMass

section Restoration

variable {α R : Type*} [Fintype α] [DecidableEq α] [Field R]

/-- Restoring the factors omitted by a complement product. -/
theorem complement_product_eq (I : Finset α) (f : α → R)
    (hf : ∀ i, f i ≠ 0) :
    (∏ i ∈ Iᶜ, f i) = (∏ i, f i) * ∏ i ∈ I, (f i)⁻¹ := by
  have hp : (∏ i ∈ I, f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  calc
    (∏ i ∈ Iᶜ, f i) = (∏ i, f i) / ∏ i ∈ I, f i :=
      (eq_div_iff hp).mpr (Finset.prod_compl_mul_prod I f)
    _ = (∏ i, f i) * ∏ i ∈ I, (f i)⁻¹ := by
      rw [div_eq_mul_inv, Finset.prod_inv_distrib]

/-- Exact restoration of independent deleted row and column factors. -/
theorem deleted_factor_restoration (I J : Finset α) (f g : α → R)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ i, g i ≠ 0) :
    (∏ i ∈ Iᶜ, f i) * (∏ j ∈ Jᶜ, g j) =
      (∏ i, f i * g i) * (∏ i ∈ I, (f i)⁻¹) * ∏ j ∈ J, (g j)⁻¹ := by
  rw [complement_product_eq I f hf, complement_product_eq J g hg,
    Finset.prod_mul_distrib]
  ring

/-- The score-factor restoration in manuscript §4.4, with explicit
nonvanishing assumptions. It does not assert the permanent bound. -/
theorem score_factor_restoration (I J : Finset α) (a : α → R)
    (hplus : ∀ i, 1 + a i ≠ 0) (hminus : ∀ i, 1 - a i ≠ 0) :
    (∏ i ∈ Iᶜ, (1 + a i)) * (∏ j ∈ Jᶜ, (1 - a j)) =
      (∏ i, (1 - (a i) ^ 2)) *
        (∏ i ∈ I, (1 + a i)⁻¹) * ∏ j ∈ J, (1 - a j)⁻¹ := by
  have hpoly : (fun i => (1 + a i) * (1 - a i)) =
      (fun i => 1 - (a i) ^ 2) := by
    funext i
    ring
  simpa only [hpoly] using
    deleted_factor_restoration I J (fun i => 1 + a i) (fun i => 1 - a i) hplus hminus

end Restoration

end Tournament
