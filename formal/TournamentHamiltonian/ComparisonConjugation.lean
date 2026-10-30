module

public import TournamentHamiltonian.ComparisonMatrix
public import TournamentHamiltonian.AlternatingTournament
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section

namespace TournamentHamiltonian

def comparisonRank (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if i.val % 2 = 0 then i.val / 2 else n - 1 - i.val / 2, by
    split_ifs <;> omega⟩

theorem comparisonRank_injective (n : ℕ) : Function.Injective (comparisonRank n) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [comparisonRank] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

noncomputable def comparisonRankEquiv (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (comparisonRank n)
    ⟨comparisonRank_injective n, Finite.surjective_of_injective (comparisonRank_injective n)⟩

@[simp] theorem comparisonRankEquiv_apply (n : ℕ) (i : Fin n) :
    comparisonRankEquiv n i = comparisonRank n i := rfl

theorem comparisonRank_zero (n : ℕ) (hn : 0 < n) :
    comparisonRankEquiv n ⟨0, hn⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  simp [comparisonRank]

def comparisonReversal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = Fin.rev j then 1 else 0

def comparisonSignedReverse (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (-1 : ℝ) ^ i.val * comparisonMatrix n i (Fin.rev j)

theorem comparisonSignedReverse_apply (n : ℕ) (i j : Fin n) :
    comparisonSignedReverse n i j =
      if i < j then (-1 : ℝ) ^ i.val else if i = j then 0 else -(-1 : ℝ) ^ j.val := by
  unfold comparisonSignedReverse
  rw [comparisonMatrix_apply]
  simp only [Fin.val_rev]
  by_cases hij : i < j
  · rw [ite_eq_left (by omega), ite_eq_left hij]
    ring
  · rw [ite_eq_right (by omega), ite_eq_right hij]
    by_cases heq : i = j
    · subst j
      rw [ite_eq_left (by omega), ite_eq_left rfl]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right heq]
      simp only [neg_one_pow_eq_ite, Nat.even_iff]
      split_ifs <;> norm_num <;> omega

theorem comparisonSignedReverse_eq_reindex_transitive (n : ℕ) :
    comparisonSignedReverse n =
      (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix
        (comparisonRankEquiv n) (comparisonRankEquiv n) := by
  ext i j
  rw [comparisonSignedReverse_apply]
  simp only [Matrix.submatrix_apply, transitiveSkew, comparisonRankEquiv_apply,
    comparisonRank, Fin.lt_def, Fin.mk.injEq,
    neg_one_pow_eq_ite, Nat.even_iff]
  split_ifs <;> norm_num <;> omega

theorem comparisonSignedReverse_eq_product (n : ℕ) :
    comparisonSignedReverse n =
      (alternatingDiagonal n : Matrix (Fin n) (Fin n) ℝ) * comparisonMatrix n *
        comparisonReversal n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [comparisonReversal, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [alternatingDiagonal, Matrix.diagonal_mul, alternatingSign,
    comparisonSignedReverse]

theorem comparisonSignedReverse_gram (n : ℕ) :
    comparisonSignedReverse n * (comparisonSignedReverse n).transpose =
      (alternatingDiagonal n : Matrix (Fin n) (Fin n) ℝ) * (comparisonMatrix n)^2 *
        alternatingDiagonal n := by
  ext i j
  simp only [alternatingDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, alternatingSign]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  change (∑ k : Fin n, comparisonSignedReverse n i k * comparisonSignedReverse n j k) = _
  calc
    _ = ∑ k : Fin n, ((-1 : ℝ)^i.val * comparisonMatrix n i k) *
        ((-1 : ℝ)^j.val * comparisonMatrix n j k) := by
      apply Fintype.sum_equiv (Fin.revPerm)
      intro k
      simp [comparisonSignedReverse, Fin.revPerm]
    _ = _ := by
      simp only [pow_two, Matrix.mul_apply]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      have h := comparisonKernel_symmetric n j.val k.val j.isLt k.isLt
      change comparisonMatrix n j k = comparisonMatrix n k j at h
      rw [h]
      ring

theorem comparison_transitive_gram_reindex (n : ℕ) :
    (-(transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)^2).submatrix
      (comparisonRankEquiv n) (comparisonRankEquiv n) =
      alternatingDiagonal n * (comparisonMatrix n)^2 * alternatingDiagonal n := by
  have ht : (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).transpose = -transitiveSkew n := by
    ext i j
    exact transitiveSkew_skew n j i
  have hg : -(transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)^2 =
      transitiveSkew n * (transitiveSkew n).transpose := by rw [ht]; noncomm_ring
  rw [hg, ← Matrix.submatrix_mul_equiv _ _ (comparisonRankEquiv n) (comparisonRankEquiv n)
    (comparisonRankEquiv n)]
  change (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix
    (comparisonRankEquiv n) (comparisonRankEquiv n) *
    ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix
    (comparisonRankEquiv n) (comparisonRankEquiv n)).transpose = _
  rw [← comparisonSignedReverse_eq_reindex_transitive]
  exact comparisonSignedReverse_gram n

theorem comparison_submatrix_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (e : Equiv.Perm (Fin n)) (p : ℕ) :
    (M ^ p).submatrix e e = (M.submatrix e e)^p := by
  induction p with
  | zero => simp
  | succ p ih => rw [pow_succ, ← Matrix.submatrix_mul_equiv _ _ e e e, ih, pow_succ]

theorem comparison_involution_conj_pow {n : ℕ} (D X : Matrix (Fin n) (Fin n) ℝ)
    (hD : D * D = 1) (p : ℕ) : (D * X * D)^p = D * X^p * D := by
  induction p with
  | zero => simpa using hD.symm
  | succ p ih =>
    rw [pow_succ, ih]
    simp only [mul_assoc]
    rw [← mul_assoc D D (X * D), hD, one_mul]
    rw [pow_succ]
    simp only [mul_assoc]

theorem comparison_transitive_gram_pow_reindex (n p : ℕ) :
    ((-(transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)^2)^p).submatrix
      (comparisonRankEquiv n) (comparisonRankEquiv n) =
      alternatingDiagonal n * ((comparisonMatrix n)^2)^p * alternatingDiagonal n := by
  rw [comparison_submatrix_pow, comparison_transitive_gram_reindex]
  exact comparison_involution_conj_pow _ _ (alternatingDiagonal_mul_self n) p

theorem comparison_pow_first_column_sq_eq_transitive_gram (n : ℕ) (hn : 0 < n) (p : ℕ) :
    (∑ i : Fin n, (((comparisonMatrix n)^p) i ⟨0,hn⟩)^2) =
      ((-(transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)^2)^p) ⟨0,hn⟩ ⟨0,hn⟩ := by
  have h := congrFun (congrFun (comparison_transitive_gram_pow_reindex n p) ⟨0,hn⟩) ⟨0,hn⟩
  simp only [Matrix.submatrix_apply, comparisonRank_zero, Matrix.mul_diagonal,
    Matrix.diagonal_mul, alternatingDiagonal, alternatingSign, Fin.val_zero,
    pow_zero, one_mul, mul_one] at h
  rw [h]
  have hp : ((comparisonMatrix n)^2)^p = (comparisonMatrix n)^p * (comparisonMatrix n)^p := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hp, Matrix.mul_apply]
  have hsym : ((comparisonMatrix n)^p).transpose = (comparisonMatrix n)^p := by
    rw [Matrix.transpose_pow, comparisonMatrix_symmetric]
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrFun (congrFun hsym i) ⟨0,hn⟩
  change ((comparisonMatrix n)^p) ⟨0,hn⟩ i = ((comparisonMatrix n)^p) i ⟨0,hn⟩ at hi
  rw [hi]
  ring

end TournamentHamiltonian
