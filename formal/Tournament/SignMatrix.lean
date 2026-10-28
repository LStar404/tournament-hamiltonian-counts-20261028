module

public import Tournament.Paths
public import Tournament.HessianPositiveRatio
public import Mathlib.Tactic.Ring

/-!
# From actual tournaments to their real sign matrices

This file connects the finite Boolean tournament model in `Paths` to the
matrix hypotheses of the paper's §2.2 and the verified algebraic Hessian
candidate. In particular, skewness and unit off-diagonal magnitude are
consequences of the tournament axioms, not additional matrix assumptions.
Regularity is defined by the actual finite outdegrees and implies zero row
sums. This bridge does not identify the candidate with an analytic Hessian.
-/

open Matrix
open scoped Matrix

@[expose] public section

namespace TournamentPaths

variable {V : Type*}

/-- The real zero-one adjacency matrix of a tournament. -/
def adjacency (T : Tournament V) : Matrix V V ℝ :=
  fun u v => if T.edge u v = true then 1 else 0

/-- The paper's sign matrix `S = A - Aᵀ`. -/
def signMatrix (T : Tournament V) : Matrix V V ℝ :=
  adjacency T - (adjacency T)ᵀ

@[simp] theorem adjacency_diag (T : Tournament V) (v : V) : adjacency T v v = 0 := by
  simp [adjacency, T.loopless]

/-- Each off-diagonal adjacency pair contains exactly one directed edge. -/
theorem adjacency_pair (T : Tournament V) (u v : V) (huv : u ≠ v) :
    adjacency T u v + adjacency T v u = 1 := by
  have hor := T.oriented u v huv
  cases h : T.edge u v <;> cases g : T.edge v u <;>
    simp_all [adjacency]

theorem signMatrix_skew (T : Tournament V) : (signMatrix T)ᵀ = -(signMatrix T) := by
  ext u v
  simp only [signMatrix, Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

@[simp] theorem signMatrix_diag (T : Tournament V) (v : V) : signMatrix T v v = 0 := by
  simp [signMatrix]

/-- All off-diagonal sign entries have square one. -/
theorem signMatrix_offdiag_sq (T : Tournament V) (u v : V) (huv : u ≠ v) :
    signMatrix T u v ^ 2 = 1 := by
  have hor := T.oriented u v huv
  cases h : T.edge u v <;> cases g : T.edge v u <;>
    simp_all [signMatrix, adjacency, Matrix.transpose_apply]

variable [Fintype V] [DecidableEq V]

/-- Actual finite outdegree, not an unconstrained scalar parameter. -/
def outDegree (T : Tournament V) (v : V) : ℕ :=
  (Finset.univ.filter fun w => T.edge v w = true).card

/-- Every vertex has exactly half of the other vertices as out-neighbors. -/
def IsRegular (T : Tournament V) : Prop :=
  ∀ v, 2 * outDegree T v + 1 = Fintype.card V

omit [DecidableEq V] in
lemma adjacency_row_sum (T : Tournament V) (v : V) :
    (∑ w, adjacency T v w) = (outDegree T v : ℝ) := by
  simp only [adjacency, outDegree, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> norm_num

/-- The paper's degree-deviation formula `s_v = 2 d_v^+ - (|V|-1)`. -/
theorem signMatrix_row_sum (T : Tournament V) (v : V) :
    (∑ w, signMatrix T v w) = 2 * (outDegree T v : ℝ) + 1 - Fintype.card V := by
  have he (w : V) : signMatrix T v w =
      2 * adjacency T v w - 1 + (if w = v then 1 else 0) := by
    by_cases hvw : v = w
    · subst w
      simp
    · have hp := adjacency_pair T v w hvw
      simp only [signMatrix, Matrix.sub_apply, Matrix.transpose_apply]
      simp only [Ne.symm hvw, ↓reduceIte]
      linarith
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    adjacency_row_sum]
  simp
  ring

/-- Regularity of the finite tournament implies the matrix zero-row-sum condition. -/
theorem regular_signMatrix_mulVec_one (T : Tournament V) (hT : IsRegular T) :
    signMatrix T *ᵥ (fun _ => 1) = 0 := by
  funext v
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply]
  rw [signMatrix_row_sum]
  have hr : (2 : ℝ) * (outDegree T v : ℝ) + 1 = (Fintype.card V : ℝ) := by
    exact_mod_cast hT v
  linarith

/-- The normalized sign matrix used in the manuscript. -/
noncomputable def normalizedSign (T : Tournament V) : Matrix V V ℝ :=
  (Fintype.card V : ℝ)⁻¹ • signMatrix T

omit [DecidableEq V] in
theorem normalizedSign_skew (T : Tournament V) :
    (normalizedSign T)ᵀ = -(normalizedSign T) := by
  simp only [normalizedSign, Matrix.transpose_smul, signMatrix_skew, smul_neg]

theorem regular_normalizedSign_mulVec_one (T : Tournament V) (hT : IsRegular T) :
    normalizedSign T *ᵥ (fun _ => 1) = 0 := by
  simp [normalizedSign, Matrix.smul_mulVec, regular_signMatrix_mulVec_one T hT]

/-- The normalized sign matrix of an actual tournament has the exact
Frobenius square `(d-1)/d`, providing the strict bound used for positivity. -/
theorem tournament_normalizedSign_frobeniusSq {n : ℕ}
    (T : Tournament (Fin (n + 1))) :
    Tournament.HessianAlgebra.frobeniusSq (normalizedSign T) =
      (((n + 1 : ℕ) : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) := by
  simpa [normalizedSign] using
    Tournament.HessianAlgebra.normalizedSign_frobeniusSq (n + 1)
      (Nat.zero_lt_succ n) (signMatrix T) (signMatrix_diag T) (signMatrix_offdiag_sq T)

/-- The algebraic Hessian candidate is positive definite for every actual
nonempty tournament. Regularity is not needed for this matrix assertion. -/
theorem tournament_algebraicHessian_posDef {n : ℕ}
    (T : Tournament (Fin (n + 1))) :
    (Tournament.HessianAlgebra.compressedResolvent n (normalizedSign T)).PosDef := by
  simpa [normalizedSign] using
    Tournament.HessianAlgebra.tournament_compressed_posDef n (signMatrix T)
      (signMatrix_skew T) (signMatrix_diag T) (signMatrix_offdiag_sq T)

/-- For a regular tournament the determinant of the verified algebraic
candidate has the exact ratio asserted in Theorem 1.2. Its identification with
the original analytic Hessian remains a separate obligation. -/
theorem regular_tournament_algebraicHessian_det {n : ℕ}
    (T : Tournament (Fin (n + 1))) (hT : IsRegular T) :
    (Tournament.HessianAlgebra.compressedResolvent n (normalizedSign T)).det =
      ((n + 1 : ℕ) : ℝ) *
        (1 + normalizedSign T * normalizedSign T).det /
        (1 - normalizedSign T * normalizedSign T).det := by
  exact Tournament.HessianAlgebra.compressedResolvent_det n (normalizedSign T)
    (normalizedSign_skew T) (regular_normalizedSign_mulVec_one T hT)

section Rational

variable {W : Type*}

/-- The same actual adjacency matrix over the rational field. -/
def rationalAdjacency (T : Tournament W) : Matrix W W ℚ :=
  fun u v => if T.edge u v = true then 1 else 0

/-- The rational sign matrix, before scalar extension. -/
def rationalSignMatrix (T : Tournament W) : Matrix W W ℚ :=
  rationalAdjacency T - (rationalAdjacency T)ᵀ

@[simp] theorem rationalAdjacency_cast_real (T : Tournament W) (u v : W) :
    (rationalAdjacency T u v : ℝ) = adjacency T u v := by
  by_cases h : T.edge u v = true <;> simp [rationalAdjacency, adjacency, h]

@[simp] theorem rationalSignMatrix_cast_real (T : Tournament W) (u v : W) :
    (rationalSignMatrix T u v : ℝ) = signMatrix T u v := by
  simp [rationalSignMatrix, signMatrix, Matrix.transpose_apply]

theorem rationalSignMatrix_skew (T : Tournament W) :
    (rationalSignMatrix T)ᵀ = -(rationalSignMatrix T) := by
  ext u v
  simp only [rationalSignMatrix, Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

variable [Fintype W]

/-- Rational normalization `S / |V|`; casts recover the existing real matrix. -/
def normalizedRationalSign (T : Tournament W) : Matrix W W ℚ :=
  (Fintype.card W : ℚ)⁻¹ • rationalSignMatrix T

theorem normalizedRationalSign_skew (T : Tournament W) :
    (normalizedRationalSign T)ᵀ = -(normalizedRationalSign T) := by
  simp only [normalizedRationalSign, Matrix.transpose_smul,
    rationalSignMatrix_skew, smul_neg]

variable [DecidableEq W]

theorem normalizedRationalSign_real (T : Tournament W) :
    Tournament.HessianAlgebra.realOfRat (normalizedRationalSign T) = normalizedSign T := by
  ext u v
  change ((normalizedRationalSign T u v : ℚ) : ℝ) = normalizedSign T u v
  simp [normalizedRationalSign, normalizedSign, Matrix.smul_apply]

theorem normalizedRationalSign_complex (T : Tournament W) :
    Tournament.HessianAlgebra.complexOfRat (normalizedRationalSign T) =
      Tournament.HessianAlgebra.complexOfReal (normalizedSign T) := by
  rw [← Tournament.HessianAlgebra.complexOfReal_realOfRat, normalizedRationalSign_real]

/-- For an actual regular tournament, the square root and determinant quotient
in Theorem 1.2 are the same strictly positive rational number. No rational-entry,
skewness, contraction, or zero-row-sum hypotheses are postulated separately.
The expression is still the algebraic Hessian candidate. -/
theorem regular_tournament_positive_rational_sqrt {n : ℕ}
    (T : Tournament (Fin (n + 1))) (hT : IsRegular T) :
    ∃ q : ℚ, 0 < q ∧
      Real.sqrt (((n + 1 : ℕ) : ℝ) /
        (Tournament.HessianAlgebra.compressedResolvent n (normalizedSign T)).det) =
          (q : ℝ) ∧
      (q : ℂ) =
        (1 + Tournament.HessianAlgebra.complexOfReal (normalizedSign T)).det /
        (1 + Complex.I • Tournament.HessianAlgebra.complexOfReal (normalizedSign T)).det := by
  have hF : Tournament.HessianAlgebra.frobeniusSq (normalizedSign T) < 1 := by
    simpa [normalizedSign] using
      Tournament.HessianAlgebra.normalizedSign_frobeniusSq_lt_one (n + 1)
        (Nat.zero_lt_succ n) (signMatrix T) (signMatrix_diag T) (signMatrix_offdiag_sq T)
  have h := Tournament.HessianAlgebra.positive_rational_sqrt_compressed n
    (normalizedRationalSign T) (normalizedRationalSign_skew T)
    (by simpa only [normalizedRationalSign_real] using hF)
    (by simpa only [normalizedRationalSign_real] using regular_normalizedSign_mulVec_one T hT)
  simpa only [normalizedRationalSign_real, normalizedRationalSign_complex] using h

end Rational

end TournamentPaths
