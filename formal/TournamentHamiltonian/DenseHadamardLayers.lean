module

public import TournamentHamiltonian.DenseTailKernel
public import TournamentHamiltonian.DenseMinorBounds
public import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false

@[expose] public section
namespace TournamentHamiltonian

/-- Entrywise Hadamard estimate for any finite real matrix, empty index included. -/
theorem dense_hadamard_entrywise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) (ht : 0 ≤ t) (hM : ∀ i j, |M i j| ≤ t) :
    |M.det| ≤ t^(Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) := by
  have hrow (i : ι) : (∑ j, M i j^2) ≤ (Fintype.card ι : ℝ)*t^2 := by
    calc
      _ ≤ ∑ _j : ι, t^2 := Finset.sum_le_sum (fun j _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (M i j)) (hM i j) 2)
      _ = _ := by simp
  have hp : (Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) =
      Real.sqrt ((Fintype.card ι : ℝ)^(Fintype.card ι)) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, mul_comm (Fintype.card ι) 2,
      pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∏ i, Real.sqrt (∑ j, M i j^2) := hadamard M
    _ ≤ ∏ _i : ι, Real.sqrt ((Fintype.card ι : ℝ)*t^2) :=
      Finset.prod_le_prod₀ (fun i _ => Real.sqrt_nonneg _) (fun i _ => Real.sqrt_le_sqrt (hrow i))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Real.sqrt_mul (Nat.cast_nonneg _),
        Real.sqrt_sq ht, mul_pow, hp]
      ring

/-- Every actual cycle principal determinant obeys the dense Hadamard bound. -/
theorem DenseStochastic.cycle_minor_hadamard {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (U : Finset (Fin n)) :
    |((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det| ≤
      (3/(n : ℝ))^U.card * Real.sqrt ((U.card : ℝ)^U.card) := by
  have h := dense_hadamard_entrywise ((-D).submatrix (Subtype.val : U → Fin n) Subtype.val)
    (3/(n : ℝ)) (by positivity) (fun i j => by
      simpa only [Matrix.submatrix_apply, Matrix.neg_apply, abs_neg,
        abs_of_nonneg (hD.nonnegative i j)] using hD.density i j)
  simpa only [Fintype.card_coe] using h

/-- Cardinal layer of the cycle coefficient, before the minor-ratio error. -/
theorem DenseStochastic.cycle_layer_hadamard {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n) (k : ℕ) :
    (∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (U.card : ℝ) * |((-D).submatrix (Subtype.val : U → Fin n) Subtype.val).det|) ≤
      (k : ℝ)*3^k*denseHadamardWeight k := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (k : ℝ)*((3/(n : ℝ))^k*Real.sqrt ((k : ℝ)^k)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hc : U.card = k := (Finset.mem_powersetCard.mp hU).2
      rw [← hc]
      exact mul_le_mul_of_nonneg_left (hD.cycle_minor_hadamard U) (Nat.cast_nonneg _)
    _ = (n.choose k : ℝ)*((k : ℝ)*((3/(n : ℝ))^k*Real.sqrt ((k : ℝ)^k))) := by
      simp [Finset.card_powersetCard]
    _ ≤ ((n : ℝ)^k/(k.factorial : ℝ))*
        ((k : ℝ)*((3/(n : ℝ))^k*Real.sqrt ((k : ℝ)^k))) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k n) (by positivity)
    _ = _ := by
      unfold denseHadamardWeight
      rw [div_pow]
      field_simp

end TournamentHamiltonian
