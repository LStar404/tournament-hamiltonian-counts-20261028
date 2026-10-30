module

public import TournamentHamiltonian.DenseHadamardLayers
public import TournamentHamiltonian.PathConvolutionGenerating

set_option autoImplicit false
@[expose] public section
namespace TournamentHamiltonian
open scoped Classical

/-- One all-ones column costs one power of the entrywise bound, not a
factor involving its inverse. In particular the estimate includes t=0. -/
theorem dense_hadamard_updateCol_ones {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hM : ∀ i j, |M i j| ≤ t) (r : ι) :
    |(M.updateCol r (fun _ => 1)).det| ≤
      t^(Fintype.card ι - 1) *
        Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) := by
  let k := Fintype.card ι
  let q := Real.sqrt (k : ℝ)
  have hk : 0 < k := Fintype.card_pos_iff.mpr ⟨r⟩
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hrow (i : ι) :
      Real.sqrt (∑ j, ((M.updateCol r (fun _ => 1)).transpose) i j ^ 2) ≤
        if i = r then q else t*q := by
    by_cases hi : i = r
    · subst i
      simp [q, k]
    · rw [ite_eq_right hi]
      have hsum : (∑ j, ((M.updateCol r (fun _ => 1)).transpose) i j ^ 2) ≤
          (k : ℝ)*t^2 := by
        calc
          _ ≤ ∑ _j : ι, t^2 := by
            apply Finset.sum_le_sum
            intro j _
            simpa [hi] using
              (pow_le_pow_left₀ (abs_nonneg (M j i)) (hM j i) 2)
          _ = _ := by simp [k]
      calc
        _ ≤ Real.sqrt ((k : ℝ)*t^2) := Real.sqrt_le_sqrt hsum
        _ = t*q := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ht]; ring
  have hp : (∏ i : ι, if i = r then q else t*q) = q * (t*q)^(k-1) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
      (fun i => if i = r then q else t*q) (Finset.mem_univ r)]
    simp only [ite_true]
    congr 1
    have heq : (∏ i ∈ (Finset.univ : Finset ι).erase r, if i = r then q else t*q) =
        ∏ _i ∈ (Finset.univ : Finset ι).erase r, t*q := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    rw [heq]
    simp [k]
  have hsqrt : q^k = Real.sqrt ((k : ℝ)^k) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k 2, pow_mul]
    rw [show q^2 = (k : ℝ) from Real.sq_sqrt (Nat.cast_nonneg _)]
  have hhad := hadamard (M.updateCol r (fun _ => 1)).transpose
  rw [Matrix.det_transpose] at hhad
  calc
    _ ≤ ∏ i, Real.sqrt (∑ j, ((M.updateCol r (fun _ => 1)).transpose) i j ^ 2) := hhad
    _ ≤ ∏ i : ι, if i = r then q else t*q :=
      Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _) (fun i _ => hrow i)
    _ = q*(t*q)^(k-1) := hp
    _ = t^(k-1)*q^k := by
      have hpow : q^(k-1)*q = q^k := by rw [← pow_succ, Nat.sub_add_cancel hk]
      calc
        _ = t^(k-1)*(q^(k-1)*q) := by rw [mul_pow]; ring
        _ = _ := by rw [hpow]
    _ = _ := by rw [hsqrt]

/-- Rank-one all-ones perturbation: terms with two marked columns vanish
in the existing determinant expansion. No sign or diagonal restriction. -/
theorem dense_hadamard_add_ones {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) (ht : 0 ≤ t) (hM : ∀ i j, |M i j| ≤ t) :
    |(M + Matrix.of (fun _ _ : ι => (1 : ℝ))).det| ≤
      t^(Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) +
      (Fintype.card ι : ℝ) * t^(Fintype.card ι - 1) *
        Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) := by
  rw [det_add_ones_eq_cols]
  calc
    _ ≤ |M.det| + |∑ r, (M.updateCol r (fun _ => 1)).det| := abs_add_le _ _
    _ ≤ |M.det| + ∑ r, |(M.updateCol r (fun _ => 1)).det| :=
      add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ t^(Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) +
        ∑ _r : ι, t^(Fintype.card ι - 1) *
          Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) := by
      apply add_le_add (dense_hadamard_entrywise M t ht hM)
      exact Finset.sum_le_sum (fun r _ => dense_hadamard_updateCol_ones M t ht hM r)
    _ = _ := by simp; ring

/-- Actual complementary determinant in the path convolution, at any U,
including the empty principal minor. -/
theorem DenseStochastic.path_minor_hadamard {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (U : Finset (Fin n)) :
    |((Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - D).submatrix
      (Subtype.val : U → Fin n) Subtype.val).det| ≤
      (3/(n : ℝ))^U.card * Real.sqrt ((U.card : ℝ)^U.card) +
      (U.card : ℝ) * (3/(n : ℝ))^(U.card-1) * Real.sqrt ((U.card : ℝ)^U.card) := by
  have h := dense_hadamard_add_ones
    ((-D).submatrix (Subtype.val : U → Fin n) Subtype.val) (3/(n : ℝ))
    (by positivity) (fun i j => by
      simpa only [Matrix.submatrix_apply, Matrix.neg_apply, abs_neg,
        abs_of_nonneg (hD.nonnegative i j)] using hD.density i j)
  have heq : ((-D).submatrix (Subtype.val : U → Fin n) Subtype.val) +
      Matrix.of (fun _ _ : U => (1 : ℝ)) =
      (Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - D).submatrix
        (Subtype.val : U → Fin n) Subtype.val := by ext i j; simp; ring
  simpa only [heq, Fintype.card_coe] using h

/-- The cardinal layer of the genuine path coefficient has a dimension-free
summable envelope after its necessary `1/n` normalization. -/
theorem DenseStochastic.path_layer_hadamard {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) (k : ℕ) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      |((Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - D).submatrix
        (Subtype.val : U → Fin n) Subtype.val).det|) / (n : ℝ) ≤
      (1 + (k : ℝ))*3^k*denseHadamardWeight k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hk : k = 0
  · subst k
    simp only [Finset.powersetCard_zero, Finset.sum_singleton, Matrix.det_isEmpty,
      abs_one, Nat.cast_zero, add_zero, pow_zero, mul_one,
      denseHadamardWeight, Nat.factorial_zero, Nat.cast_one, div_one, Real.sqrt_one]
    exact (div_le_one hnR).mpr hn1
  have hk1 : 1 ≤ k := by omega
  have hpow (x : ℝ) : x^k = x^(k-1)*x := by rw [← pow_succ, Nat.sub_add_cancel hk1]
  calc
    _ ≤ ((n.choose k : ℝ) * ((3/(n : ℝ))^k * Real.sqrt ((k : ℝ)^k) +
        (k : ℝ) * (3/(n : ℝ))^(k-1) * Real.sqrt ((k : ℝ)^k))) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      calc
        _ ≤ ∑ _U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            ((3/(n : ℝ))^k * Real.sqrt ((k : ℝ)^k) +
              (k : ℝ) * (3/(n : ℝ))^(k-1) * Real.sqrt ((k : ℝ)^k)) := by
          apply Finset.sum_le_sum
          intro U hU
          have hc : U.card = k := (Finset.mem_powersetCard.mp hU).2
          simpa only [hc] using hD.path_minor_hadamard U
        _ = _ := by simp [Finset.card_powersetCard]; ring
    _ ≤ (((n : ℝ)^k/(k.factorial : ℝ)) *
        ((3/(n : ℝ))^k * Real.sqrt ((k : ℝ)^k) +
          (k : ℝ) * (3/(n : ℝ))^(k-1) * Real.sqrt ((k : ℝ)^k))) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k n) (by positivity)
    _ = ((1/(n : ℝ)) + (k : ℝ)/3) * 3^k * denseHadamardWeight k := by
      unfold denseHadamardWeight
      simp only [div_pow]
      rw [hpow (n : ℝ), hpow 3]
      field_simp
    _ ≤ (1 + (k : ℝ))*3^k*denseHadamardWeight k := by
      apply mul_le_mul_of_nonneg_right _ (by unfold denseHadamardWeight; positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hfirst : (1 : ℝ)/n ≤ 1 := (div_le_one hnR).mpr hn1
      have hsecond : (k : ℝ)/3 ≤ k := by nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
      exact add_le_add hfirst hsecond

end TournamentHamiltonian
