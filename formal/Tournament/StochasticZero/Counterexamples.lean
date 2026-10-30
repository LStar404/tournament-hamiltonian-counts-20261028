module

public import Tournament.StochasticZero.Core
public import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Matrix

@[expose] public section

namespace StochasticZero.Counterexamples

/-- Directed three-cycle, without the diagonal laziness required in the theorem. -/
def cycleP : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
def cycleU : Fin 3 → ℂ := ![-1, -1, 1]
def cycleV : Fin 3 → ℂ := ![1, -1, -1]

theorem cycleP_nonneg : ∀ i j, 0 ≤ cycleP i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [cycleP]

theorem cycleP_stochastic : ∀ i, ∑ j, cycleP i j = 1 := by
  intro i; fin_cases i <;> norm_num [cycleP, Fin.sum_univ_succ]

theorem cycleP_connected : ∀ i j, PositiveReachable cycleP i j := by
  have h01 : 0 < cycleP 0 1 := by norm_num [cycleP]
  have h12 : 0 < cycleP 1 2 := by norm_num [cycleP]
  have h20 : 0 < cycleP 2 0 := by norm_num [cycleP]
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h01
  · exact (Relation.ReflTransGen.single (r := fun a b => 0 < cycleP a b) h01).tail h12
  · exact (Relation.ReflTransGen.single (r := fun a b => 0 < cycleP a b) h12).tail h20
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h12
  · exact Relation.ReflTransGen.single h20
  · exact (Relation.ReflTransGen.single (r := fun a b => 0 < cycleP a b) h20).tail h01
  · exact Relation.ReflTransGen.refl

theorem cycleU_norm : ∀ j, ‖cycleU j‖ ≤ 1 := by
  intro j; fin_cases j <;> norm_num [cycleU]

theorem cycleV_ne_zero : cycleV ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [cycleV] at this

theorem cycleV_fixed : ∀ i, cycleV i = ∑ j, (cycleP i j : ℂ) * cycleU j * cycleV j := by
  intro i; fin_cases i <;> norm_num [cycleP, cycleU, cycleV, Fin.sum_univ_succ]

theorem cycleU_not_one : ¬ ∀ j, cycleU j = 1 := by
  intro h
  have := h 0
  norm_num [cycleU] at this

theorem cycleP_diagonal_zero : ∀ i, cycleP i i = 0 := by
  intro i; fin_cases i <;> norm_num [cycleP]

/-- Executable logical attack: every hypothesis except the positive diagonal holds,
yet the actual determinant vanishes away from the all-ones point. -/
theorem positive_diagonal_is_essential :
    (twistedMatrix cycleP cycleU).det = 0 ∧ ¬ (∀ j, cycleU j = 1) := by
  refine ⟨?_, cycleU_not_one⟩
  exact Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨cycleV, cycleV_ne_zero, (twistedMatrix_mulVec_eq_zero_iff _ _ _).mpr cycleV_fixed⟩

/-- Disconnected stochastic matrix with a positive diagonal. -/
def disconnectedP : Matrix (Fin 2) (Fin 2) ℝ := 1
def disconnectedU : Fin 2 → ℂ := ![1, 0]
def disconnectedV : Fin 2 → ℂ := ![1, 0]

theorem disconnectedP_nonneg : ∀ i j, 0 ≤ disconnectedP i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply, disconnectedP]

theorem disconnectedP_stochastic : ∀ i, ∑ j, disconnectedP i j = 1 := by
  intro i; fin_cases i <;> norm_num [Matrix.one_apply, disconnectedP, Fin.sum_univ_succ]

theorem disconnectedP_diagonal : ∀ i, 0 < disconnectedP i i := by
  intro i; norm_num [Matrix.one_apply, disconnectedP]

theorem disconnectedU_norm : ∀ j, ‖disconnectedU j‖ ≤ 1 := by
  intro j; fin_cases j <;> norm_num [disconnectedU]

/-- Executable attack on deleting the connectivity hypothesis. -/
theorem connectivity_is_essential :
    (twistedMatrix disconnectedP disconnectedU).det = 0 ∧
    ¬ (∀ j, disconnectedU j = 1) := by
  constructor
  · apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨disconnectedV, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      norm_num [disconnectedV] at this
    · apply (twistedMatrix_mulVec_eq_zero_iff _ _ _).mpr
      intro i
      fin_cases i <;> norm_num [Matrix.one_apply, disconnectedP, disconnectedU, disconnectedV, Fin.sum_univ_succ]
  · intro h
    have := h 1
    norm_num [disconnectedU] at this

/-- Empty dimension is deliberately excluded from the equivalence: the
all-ones condition is vacuous but the determinant is one, not zero. -/
theorem empty_dimension_boundary (P : Matrix (Fin 0) (Fin 0) ℝ) (u : Fin 0 → ℂ) :
    (twistedMatrix P u).det = 1 ∧ (∀ j, u j = 1) := by
  exact ⟨Matrix.det_isEmpty, fun j => Fin.elim0 j⟩

end StochasticZero.Counterexamples
