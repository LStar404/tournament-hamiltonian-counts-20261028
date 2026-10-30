module

public import TournamentHamiltonian.Equality.RegularCarousel
public import TournamentHamiltonian.MatrixPowerDefs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.ModEq

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- The actual Boolean tournament sign matrix with integer coefficients. -/
def intSignMatrix {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j then 0 else if T.val i j then 1 else -1

theorem intSignMatrix_cast_real {n : ℕ} (T : Tournament n) (i j : Fin n) :
    (intSignMatrix T i j : ℝ) = signMatrix T i j := by
  simp [intSignMatrix, signMatrix]

theorem intSignMatrix_skew {n : ℕ} (T : Tournament n) (i j : Fin n) :
    intSignMatrix T i j = -intSignMatrix T j i := by
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_neg, intSignMatrix_cast_real] using signMatrix_skew T i j

/-- The mod-two sign matrix is `J + I` at every order, including zero. -/
theorem intSignMatrix_mod_two {n : ℕ} (T : Tournament n) :
    (intSignMatrix T).map (Int.castRingHom (ZMod 2)) =
      Matrix.of (fun _ _ : Fin n => (1 : ZMod 2)) + 1 := by
  ext i j
  by_cases hij : i = j
  · subst j; norm_num [intSignMatrix, Matrix.one_apply]; decide
  · cases h : T.val i j <;> norm_num [intSignMatrix, hij, h, Matrix.one_apply]
    all_goals decide

/-- The parity computation is uniform in the cardinality; it does not assume `n` odd. -/
theorem one_add_allOnes_cube_mod_two (n : ℕ) :
    (Matrix.of (fun _ _ : Fin n => (1 : ZMod 2)) + 1) ^ 3 =
      Matrix.of (fun _ _ : Fin n => (1 : ZMod 2)) + 1 := by
  let J : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of (fun _ _ => 1)
  change (J + 1) ^ 3 = J + 1
  have hJJ : J * J = (n : ZMod 2) • J := by
    ext i j
    simp [J, Matrix.mul_apply]
  have hn : (n : ZMod 2) = 0 ∨ (n : ZMod 2) = 1 := by
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact h n
  calc
    _ = J * J * J + (J * J + J * J + J * J) + (J + J + J) + 1 := by noncomm_ring
    _ = J + 1 := by
      rw [hJJ, Matrix.smul_mul, hJJ, smul_smul]
      ext i j
      rcases hn with hn | hn <;> norm_num [hn, J] <;> decide

/-- Cubing preserves the off-diagonal odd parity of every tournament sign matrix. -/
theorem intSignMatrix_cube_mod_two {n : ℕ} (T : Tournament n) :
    ((intSignMatrix T) ^ 3).map (Int.castRingHom (ZMod 2)) =
      Matrix.of (fun _ _ : Fin n => (1 : ZMod 2)) + 1 := by
  rw [Matrix.map_pow, intSignMatrix_mod_two, one_add_allOnes_cube_mod_two]

theorem intSignMatrix_cube_odd {n : ℕ} (T : Tournament n) (i j : Fin n) (hij : i ≠ j) :
    Odd ((intSignMatrix T ^ 3) i j) := by
  apply ZMod.intCast_eq_one_iff_odd.mp
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A i j)
    (intSignMatrix_cube_mod_two T)
  simpa [Matrix.one_apply, hij] using h

theorem intSignMatrix_cube_skew {n : ℕ} (T : Tournament n) (i j : Fin n) :
    (intSignMatrix T ^ 3) i j = -(intSignMatrix T ^ 3) j i := by
  have hT : (intSignMatrix T).transpose = -intSignMatrix T := by
    ext a b
    exact intSignMatrix_skew T b a
  have hcube : (intSignMatrix T ^ 3).transpose = -(intSignMatrix T ^ 3) := by
    rw [Matrix.transpose_pow, hT, neg_pow]
    norm_num
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℤ => A j i) hcube

theorem intSignMatrix_cube_diag {n : ℕ} (T : Tournament n) (i : Fin n) :
    (intSignMatrix T ^ 3) i i = 0 := by
  have := intSignMatrix_cube_skew T i i
  omega

/-- An odd integer square differs from one by a multiple of eight. -/
theorem eight_dvd_odd_sq_sub_one (z : ℤ) (hz : Odd z) : 8 ∣ z ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hz
  have hk : 2 ∣ k * (k + 1) := Int.two_dvd_mul_add_one k
  obtain ⟨l, hl⟩ := hk
  refine ⟨l, ?_⟩
  nlinarith

/-- Pairing a symmetric, zero-diagonal array doubles every off-diagonal divisor.
This is an exact finite sum argument, including the empty array. -/
theorem two_mul_dvd_sum_symmetric (k : ℤ) (n : ℕ)
    (f : Fin n → Fin n → ℤ) (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) (hdiv : ∀ i j, i ≠ j → k ∣ f i j) :
    2 * k ∣ ∑ i, ∑ j, f i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htop : 2 * k ∣ ∑ i : Fin n, ∑ j : Fin n, f i.castSucc j.castSucc :=
      ih (fun i j => f i.castSucc j.castSucc)
        (fun i j => hsymm _ _) (fun i => hdiag _)
        (fun i j hij => hdiv _ _ (fun h => hij (Fin.castSucc_injective n h)))
    have hrow : k ∣ ∑ i : Fin n, f i.castSucc (Fin.last n) := by
      apply Finset.dvd_sum
      intro i _
      exact hdiv _ _ (Fin.castSucc_ne_last i)
    have heq : (∑ i : Fin (n + 1), ∑ j, f i j) =
        (∑ i : Fin n, ∑ j : Fin n, f i.castSucc j.castSucc) +
        2 * ∑ i : Fin n, f i.castSucc (Fin.last n) := by
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.sum_univ_castSucc]
      rw [Finset.sum_add_distrib, hdiag, add_zero]
      have hs : (∑ i : Fin n, f (Fin.last n) i.castSucc) =
          ∑ i : Fin n, f i.castSucc (Fin.last n) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsymm _ _
      rw [hs]
      ring
    obtain ⟨a, ha⟩ := htop
    obtain ⟨b, hb⟩ := hrow
    refine ⟨a + b, ?_⟩
    rw [heq, ha, hb]
    ring

/-- Integer Frobenius square of the actual matrix. -/
def intMatrixFrobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∑ i, ∑ j, A i j ^ 2

/-- Exact count of the ordered off-diagonal positions, with integer subtraction. -/
theorem sum_off_diagonal_ones (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i = j then (0 : ℤ) else 1) =
      (n : ℤ) * (n - 1) := by
  have hrow (i : Fin n) :
      (∑ j : Fin n, if i = j then (0 : ℤ) else 1) = n - 1 := by
    calc
      _ = ∑ j : Fin n, ((1 : ℤ) - if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by simp [Finset.sum_sub_distrib]
  simp [hrow]
  ring

/-- The sixth-moment congruence, for every genuine tournament and every order.
The diagonal is zero, off-diagonal cube entries are odd, and skew pairing supplies
16 rather than only 8. -/
theorem sixteen_dvd_intSignMatrix_cube_frob_sub (n : ℕ) (T : Tournament n) :
    16 ∣ intMatrixFrobSq (intSignMatrix T ^ 3) - (n : ℤ) * (n - 1) := by
  let f : Fin n → Fin n → ℤ := fun i j =>
    (intSignMatrix T ^ 3) i j ^ 2 - if i = j then 0 else 1
  have hpair : 16 ∣ ∑ i, ∑ j, f i j := by
    apply two_mul_dvd_sum_symmetric 8 n f
    · intro i j
      dsimp [f]
      rw [intSignMatrix_cube_skew T i j]
      simp [eq_comm]
    · intro i
      simp [f, intSignMatrix_cube_diag]
    · intro i j hij
      simpa [f, hij] using eight_dvd_odd_sq_sub_one _ (intSignMatrix_cube_odd T i j hij)
  simpa [f, Finset.sum_sub_distrib, intMatrixFrobSq, sum_off_diagonal_ones] using hpair

/-- Any two same-order tournament sixth moments differ by a multiple of sixteen. -/
theorem sixteen_dvd_intSignMatrix_cube_frob_sub_cube_frob {n : ℕ}
    (T U : Tournament n) :
    16 ∣ intMatrixFrobSq (intSignMatrix T ^ 3) - intMatrixFrobSq (intSignMatrix U ^ 3) := by
  have hT := sixteen_dvd_intSignMatrix_cube_frob_sub n T
  have hU := sixteen_dvd_intSignMatrix_cube_frob_sub n U
  simpa only [sub_sub_sub_cancel_right] using dvd_sub hT hU

/-- The integer construction maps to the existing real sign-matrix powers. -/
theorem intSignMatrix_pow_cast_real {n : ℕ} (T : Tournament n) (p : ℕ) :
    ((intSignMatrix T) ^ p).map (Int.castRingHom ℝ) = signMatrix T ^ p := by
  rw [Matrix.map_pow]
  congr 1
  ext i j
  exact intSignMatrix_cast_real T i j

/-- No surrogate norm: the cast is the pre-existing real `matrixFrobSq`. -/
theorem intSignMatrix_frob_pow_cast_real {n : ℕ} (T : Tournament n) (p : ℕ) :
    (intMatrixFrobSq (intSignMatrix T ^ p) : ℝ) = matrixFrobSq (signMatrix T ^ p) := by
  have heq (i j : Fin n) : ((intSignMatrix T ^ p) i j : ℝ) = (signMatrix T ^ p) i j :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) (intSignMatrix_pow_cast_real T p)
  simp only [intMatrixFrobSq, matrixFrobSq, Int.cast_sum, Int.cast_pow, heq]

/-- The actual real sixth-moment difference is sixteen times an integer. -/
theorem tournament_sixth_moment_difference_mul_sixteen {n : ℕ} (T U : Tournament n) :
    ∃ k : ℤ, matrixFrobSq (signMatrix T ^ 3) - matrixFrobSq (signMatrix U ^ 3) =
      16 * (k : ℝ) := by
  obtain ⟨k, hk⟩ := sixteen_dvd_intSignMatrix_cube_frob_sub_cube_frob T U
  refine ⟨k, ?_⟩
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hk
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    intSignMatrix_frob_pow_cast_real] using hc

/-- Arithmetic quantization of any strict sixth-moment difference between two
same-order actual tournaments. Strictness is an explicit input to this arithmetic
lemma; it is not assumed by the classification theorems. -/
theorem tournament_sixth_moment_gap_at_least_sixteen {n : ℕ} (T U : Tournament n)
    (hstrict : matrixFrobSq (signMatrix U ^ 3) < matrixFrobSq (signMatrix T ^ 3)) :
    16 ≤ matrixFrobSq (signMatrix T ^ 3) - matrixFrobSq (signMatrix U ^ 3) := by
  obtain ⟨k, hk⟩ := tournament_sixth_moment_difference_mul_sixteen T U
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkposZ : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hkoneZ : (1 : ℤ) ≤ k := by omega
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkoneZ
  linarith

/-- The manuscript's quantitative `Δ₃ ≥ 16` arithmetic step, in terms of its
actual transitive matrix and the actual tournament matrix. -/
theorem transitive_sixth_moment_gap_at_least_sixteen {n : ℕ} (T : Tournament n)
    (hstrict : matrixFrobSq (signMatrix T ^ 3) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 3)) :
    16 ≤ matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 3) -
      matrixFrobSq (signMatrix T ^ 3) := by
  simpa only [signMatrix_transitiveTournament] using
    tournament_sixth_moment_gap_at_least_sixteen (transitiveTournament n) T
      (by simpa only [signMatrix_transitiveTournament] using hstrict)

end TournamentHamiltonian.Equality
