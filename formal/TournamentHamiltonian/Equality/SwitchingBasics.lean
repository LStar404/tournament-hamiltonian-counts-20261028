module

public import TournamentHamiltonian.Equality.PfaffianFour
public import TournamentHamiltonian.TransitiveDeterminant
public import Mathlib.Data.Finset.Sort

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- Entrywise form of diagonal conjugation by the signs `ε`. -/
def switch {ι : Type*} (S : Matrix ι ι ℝ) (ε : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ε i * S i j * ε j

/-- Four distinct vertices, in any order, induce determinant one. -/
def AllFourDetOne {ι : Type*} (S : Matrix ι ι ℝ) : Prop :=
  ∀ f : Fin 4 → ι, Function.Injective f → (S.submatrix f f).det = 1

/-- A real sign matrix is a skew matrix whose off-diagonal entries are signs. -/
structure IsSkewSign {ι : Type*} (S : Matrix ι ι ℝ) : Prop where
  skew : ∀ i j, S i j = -S j i
  signs : ∀ i j, i ≠ j → S i j = 1 ∨ S i j = -1

theorem signMatrix_isSkewSign {n : ℕ} (T : Tournament n) : IsSkewSign (signMatrix T) := by
  refine ⟨signMatrix_skew T, ?_⟩
  intro i j hij
  cases h : T.val i j <;> simp [signMatrix, hij, h]

theorem IsSkewSign.diag {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSkewSign S) (i : ι) :
    S i i = 0 := by have := hS.skew i i; linarith

theorem switch_eq_diagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (ε : ι → ℝ) :
    switch S ε = Matrix.diagonal ε * S * Matrix.diagonal ε := by
  ext i j
  simp [switch, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Diagonal sign conjugation preserves the actual determinant. -/
theorem det_switch {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (ε : ι → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    (switch S ε).det = S.det := by
  rw [switch_eq_diagonal_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hprod : (∏ i, ε i) ^ 2 = 1 := by rw [← Finset.prod_pow]; simp [hε]
  calc
    _ = S.det * (∏ i, ε i) ^ 2 := by ring
    _ = S.det := by rw [hprod, mul_one]

theorem allFourDetOne_switch_iff {ι : Type*} (S : Matrix ι ι ℝ)
    (ε : ι → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    AllFourDetOne (switch S ε) ↔ AllFourDetOne S := by
  have hdet (f : Fin 4 → ι) : ((switch S ε).submatrix f f).det = (S.submatrix f f).det :=
    det_switch (S.submatrix f f) (ε ∘ f) (fun i => hε (f i))
  simp only [AllFourDetOne, hdet]

theorem IsSkewSign.switch {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSkewSign S)
    (ε : ι → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) : IsSkewSign (switch S ε) := by
  refine ⟨?_, ?_⟩
  · intro i j
    dsimp [Equality.switch]
    rw [hS.skew i j]
    ring
  · intro i j hij
    rcases hε i with hi | hi <;> rcases hε j with hj | hj <;>
      rcases hS.signs i j hij with hs | hs <;> simp [Equality.switch, hi, hj, hs]

/-- The canonical pivot switching turns all edges from `p` outward. -/
def pivotSigns {ι : Type*} [DecidableEq ι] (S : Matrix ι ι ℝ) (p : ι) (i : ι) : ℝ :=
  if i = p then 1 else S p i

theorem pivotSigns_signs {ι : Type*} [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsSkewSign S) (p i : ι) : pivotSigns S p i = 1 ∨ pivotSigns S p i = -1 := by
  by_cases hi : i = p
  · simp [pivotSigns, hi]
  · simpa [pivotSigns, hi] using hS.signs p i (Ne.symm hi)

theorem switch_pivot_row {ι : Type*} [DecidableEq ι] {S : Matrix ι ι ℝ}
    (hS : IsSkewSign S) (p i : ι) (hi : i ≠ p) :
    switch S (pivotSigns S p) p i = 1 := by
  rcases hS.signs p i (Ne.symm hi) with hs | hs <;>
    simp [switch, pivotSigns, hi, hs]

end TournamentHamiltonian.Equality
