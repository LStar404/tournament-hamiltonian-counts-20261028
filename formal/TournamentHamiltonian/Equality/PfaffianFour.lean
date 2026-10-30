module

public import TournamentHamiltonian.Definitions
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- The six independent upper entries of a four by four skew matrix. -/
def skewFour (a b c g e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, a, b, c; -a, 0, g, e; -b, -g, 0, f; -c, -e, -f, 0]

/-- The actual determinant, not a separately defined Pfaffian surrogate. -/
theorem det_skewFour (a b c g e f : ℝ) :
    (skewFour a b c g e f).det = (a * f - b * e + c * g) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [skewFour, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Every four by four real skew matrix satisfies the Pfaffian square identity. -/
theorem det_skew_four (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hskew : ∀ i j, S i j = -S j i) :
    S.det = (S 0 1 * S 2 3 - S 0 2 * S 1 3 + S 0 3 * S 1 2) ^ 2 := by
  have hdiag (i : Fin 4) : S i i = 0 := by have := hskew i i; linarith
  have heq : S = skewFour (S 0 1) (S 0 2) (S 0 3) (S 1 2) (S 1 3) (S 2 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewFour, hdiag] <;> apply hskew
  conv_lhs => rw [heq]
  exact det_skewFour _ _ _ _ _ _

/-- For sign entries, the only fourth principal determinant values are one and nine. -/
theorem det_skewFour_eq_one_or_nine (a b c g e f : ℝ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hg : g = 1 ∨ g = -1)
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1) :
    (skewFour a b c g e f).det = 1 ∨ (skewFour a b c g e f).det = 9 := by
  rw [det_skewFour]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hg with rfl | rfl <;>
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> norm_num

/-- A dominating pivot above a directed triangle forces determinant nine. -/
theorem det_dominating_triangle (t : ℝ) (ht : t = 1 ∨ t = -1) :
    (skewFour 1 1 1 t (-t) t).det = 9 := by
  rw [det_skewFour]
  rcases ht with rfl | rfl <;> norm_num

end TournamentHamiltonian.Equality
