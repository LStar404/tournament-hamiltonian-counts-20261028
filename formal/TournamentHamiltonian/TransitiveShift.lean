module

public import TournamentHamiltonian.MatrixPowerDefs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Signed cyclic invariance of the real transitive matrix and its Gram powers. -/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

def transitiveCycleSucc (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val < n then ⟨i.val + 1, by omega⟩ else 0

theorem transitiveCycleSucc_injective (n : ℕ) : Function.Injective (transitiveCycleSucc n) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [transitiveCycleSucc] at hv
  split_ifs at hv <;> simp only [Fin.val_zero] at hv <;>
    apply Fin.ext <;> omega

noncomputable def transitiveCycleEquiv (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (transitiveCycleSucc n)
    ⟨transitiveCycleSucc_injective n, Finite.surjective_of_injective (transitiveCycleSucc_injective n)⟩

def transitiveCycleSign (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val < n then 1 else -1

theorem transitiveCycleSign_sq (n : ℕ) (i : Fin (n + 1)) :
    transitiveCycleSign n i * transitiveCycleSign n i = 1 := by
  unfold transitiveCycleSign
  split_ifs <;> norm_num

def transitiveSignedRotate (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => transitiveCycleSign n i * transitiveCycleSign n j *
    M (transitiveCycleSucc n i) (transitiveCycleSucc n j)

theorem transitiveSignedRotate_one (n : ℕ) :
    transitiveSignedRotate n (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [transitiveSignedRotate, transitiveCycleSign_sq]
  · have hr : transitiveCycleSucc n i ≠ transitiveCycleSucc n j :=
      fun he => h (transitiveCycleSucc_injective n he)
    simp [transitiveSignedRotate, h, hr]

theorem transitiveSignedRotate_mul (n : ℕ)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    transitiveSignedRotate n (A * B) = transitiveSignedRotate n A * transitiveSignedRotate n B := by
  ext i j
  simp only [transitiveSignedRotate, Matrix.mul_apply]
  rw [Finset.mul_sum]
  calc
    _ = ∑ k : Fin (n + 1), transitiveCycleSign n i * transitiveCycleSign n j *
        (A (transitiveCycleSucc n i) (transitiveCycleSucc n k) *
          B (transitiveCycleSucc n k) (transitiveCycleSucc n j)) := by
      exact (Equiv.sum_comp (transitiveCycleEquiv n) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hk := transitiveCycleSign_sq n k
      calc
        _ = (transitiveCycleSign n k * transitiveCycleSign n k) *
            (transitiveCycleSign n i * transitiveCycleSign n j *
              (A (transitiveCycleSucc n i) (transitiveCycleSucc n k) *
                B (transitiveCycleSucc n k) (transitiveCycleSucc n j))) := by rw [hk, one_mul]
        _ = _ := by ring

theorem transitiveSignedRotate_neg (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    transitiveSignedRotate n (-A) = -transitiveSignedRotate n A := by
  ext i j
  simp [transitiveSignedRotate]

theorem transitiveSignedRotate_pow (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p : ℕ) :
    transitiveSignedRotate n (A ^ p) = (transitiveSignedRotate n A) ^ p := by
  induction p with
  | zero => simp [transitiveSignedRotate_one]
  | succ p ih => rw [pow_succ, transitiveSignedRotate_mul, ih, pow_succ]

theorem transitiveSignedRotate_transitive (n : ℕ) :
    transitiveSignedRotate n (transitiveSkew (n + 1) : Matrix _ _ ℝ) = transitiveSkew (n + 1) := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n
  · have hij : transitiveCycleSucc n i < transitiveCycleSucc n j ↔ i < j := by
      simp only [transitiveCycleSucc, dite_eq_left hi, dite_eq_left hj]
      change i.val + 1 < j.val + 1 ↔ i.val < j.val
      omega
    have hji : transitiveCycleSucc n j < transitiveCycleSucc n i ↔ j < i := by
      simp only [transitiveCycleSucc, dite_eq_left hi, dite_eq_left hj]
      change j.val + 1 < i.val + 1 ↔ j.val < i.val
      omega
    simp only [transitiveSignedRotate, transitiveCycleSign, ite_eq_left hi, ite_eq_left hj,
      one_mul, transitiveSkew, hij, hji]
  · have hjlast : j.val = n := by omega
    have hij : i < j := by exact_mod_cast (show i.val < j.val by omega)
    simp [transitiveSignedRotate, transitiveCycleSign, transitiveCycleSucc,
      hi, hj, transitiveSkew, hij, not_lt_of_ge hij.le, hjlast]
  · have hilast : i.val = n := by omega
    have hji : j < i := by exact_mod_cast (show j.val < i.val by omega)
    simp [transitiveSignedRotate, transitiveCycleSign, transitiveCycleSucc,
      hi, hj, transitiveSkew, hji, not_lt_of_ge hji.le, hilast]
  · have hij : i = j := Fin.ext (by omega)
    subst j
    simp [transitiveSignedRotate, transitiveSkew]

def transitiveSignedShift (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = transitiveCycleSucc n j then transitiveCycleSign n j else 0

theorem transitiveSignedShift_conjugation (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (transitiveSignedShift n).transpose * A * transitiveSignedShift n =
      transitiveSignedRotate n A := by
  ext i j
  simp [Matrix.mul_apply, transitiveSignedShift, Matrix.transpose_apply,
    transitiveSignedRotate, mul_comm, mul_left_comm, mul_assoc]

theorem transitiveSignedShift_transpose_mul (n : ℕ) :
    (transitiveSignedShift n).transpose * transitiveSignedShift n = 1 := by
  simpa only [Matrix.mul_one] using
    (transitiveSignedShift_conjugation n 1).trans (transitiveSignedRotate_one n)

theorem transitiveSignedShift_mul_transpose (n : ℕ) :
    transitiveSignedShift n * (transitiveSignedShift n).transpose = 1 :=
  mul_eq_one_comm.mp (transitiveSignedShift_transpose_mul n)

theorem transitive_signed_shift_conjugation (n : ℕ) :
    (transitiveSignedShift n).transpose *
      (transitiveSkew (n + 1) : Matrix _ _ ℝ) * transitiveSignedShift n =
        transitiveSkew (n + 1) :=
  (transitiveSignedShift_conjugation n _).trans (transitiveSignedRotate_transitive n)

theorem transitive_gram_pow_rotate_fixed (n p : ℕ) :
    transitiveSignedRotate n
      ((-((transitiveSkew (n + 1) : Matrix _ _ ℝ) ^ 2)) ^ p) =
        (-((transitiveSkew (n + 1) : Matrix _ _ ℝ) ^ 2)) ^ p := by
  rw [transitiveSignedRotate_pow, transitiveSignedRotate_neg,
    transitiveSignedRotate_pow, transitiveSignedRotate_transitive]

theorem diagonal_constant_of_transitiveSignedRotate (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : transitiveSignedRotate n M = M) (i j : Fin (n + 1)) : M i i = M j j := by
  have hstep (k : Fin (n + 1)) : M (transitiveCycleSucc n k) (transitiveCycleSucc n k) = M k k := by
    have h := congrFun (congrFun hM k) k
    change transitiveCycleSign n k * transitiveCycleSign n k *
      M (transitiveCycleSucc n k) (transitiveCycleSucc n k) = M k k at h
    simpa only [transitiveCycleSign_sq, one_mul] using h
  have hzero : ∀ (k : ℕ) (hk : k < n + 1), M ⟨k, hk⟩ ⟨k, hk⟩ = M 0 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hs := hstep ⟨k, by omega⟩
      simpa only [transitiveCycleSucc, hkn, dite_true] using hs.trans (ih (by omega))
  exact (hzero i.val i.isLt).trans (hzero j.val j.isLt).symm

/-- Every Gram-power diagonal is constant, without a parity restriction on n or p. -/
theorem transitive_gram_pow_diagonal_constant (n p : ℕ) (i j : Fin n) :
    ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) i i =
      ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) j j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      exact diagonal_constant_of_transitiveSignedRotate n _
        (transitive_gram_pow_rotate_fixed n p) i j

theorem transitive_gram_pow_trace_eq_card_mul_diag (n : ℕ) (hn : 0 < n) (p : ℕ) :
    Matrix.trace ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) =
      (n : ℝ) * ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) ⟨0, hn⟩ ⟨0, hn⟩ := by
  calc
    _ = ∑ i : Fin n, ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) i i := rfl
    _ = ∑ _i : Fin n, ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) ⟨0, hn⟩ ⟨0, hn⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      exact transitive_gram_pow_diagonal_constant n p i ⟨0, hn⟩
    _ = _ := by simp

theorem matrixFrobSq_eq_trace_mul_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobSq A = Matrix.trace (A * A.transpose) := by
  simp [matrixFrobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]

theorem matrixFrobSq_pow_eq_trace_neg_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = -A) (p : ℕ) :
    matrixFrobSq (A ^ p) = Matrix.trace ((-(A ^ 2)) ^ p) := by
  rw [matrixFrobSq_eq_trace_mul_transpose, Matrix.transpose_pow, hA]
  have hc : Commute A (-A) := (Commute.refl A).neg_right
  rw [← hc.mul_pow]
  congr 2
  noncomm_ring

theorem real_transitiveSkew_transpose (n : ℕ) :
    (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).transpose = -transitiveSkew n := by
  ext i j
  exact transitiveSkew_skew n j i

theorem transitive_frob_pow_eq_card_mul_diag (n : ℕ) (hn : 0 < n) (p : ℕ) :
    matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) =
      (n : ℝ) * ((-((transitiveSkew n : Matrix _ _ ℝ) ^ 2)) ^ p) ⟨0, hn⟩ ⟨0, hn⟩ := by
  rw [matrixFrobSq_pow_eq_trace_neg_sq _ (real_transitiveSkew_transpose n)]
  exact transitive_gram_pow_trace_eq_card_mul_diag n hn p

end TournamentHamiltonian
