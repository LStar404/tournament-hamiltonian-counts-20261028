module

public import TournamentHamiltonian.MatrixPowerDefs
public import TournamentHamiltonian.Equality.PfaffianFour

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

open scoped BigOperators Matrix

/-- Four independent finite indices, including repeated vertices. -/
def sumFour {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, f i j k l

theorem sumFour_swap_middle {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    sumFour f = sumFour (fun i j k l => f i k j l) := by
  unfold sumFour
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem sumFour_swap_last {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    sumFour f = sumFour (fun i j k l => f i j l k) := by
  unfold sumFour
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem sumFour_congr {n : ℕ} {f g : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j k l, f i j k l = g i j k l) : sumFour f = sumFour g := by
  unfold sumFour
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  exact h i j k l

theorem sumFour_mul_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    sumFour (fun i j k l => A i j ^ 2 * A k l ^ 2) = matrixFrobSq A ^ 2 := by
  simp only [sumFour, matrixFrobSq, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem sumFour_mul_sq_middle {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    sumFour (fun i j k l => A i k ^ 2 * A j l ^ 2) = matrixFrobSq A ^ 2 := by
  rw [sumFour_swap_middle]
  exact sumFour_mul_sq A

theorem sumFour_mul_sq_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    sumFour (fun i j k l => A i l ^ 2 * A j k ^ 2) = matrixFrobSq A ^ 2 := by
  rw [sumFour_swap_last]
  exact sumFour_mul_sq_middle A

/-- The first crossing term is exactly the squared Frobenius norm of A². -/
theorem sumFour_cross_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    sumFour (fun i j k l => (A i j * A k l) * (A i k * A j l)) =
      matrixFrobSq (A ^ 2) := by
  rw [sumFour_swap_last, sumFour_swap_middle]
  simp only [sumFour, matrixFrobSq, pow_two, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem sumFour_cross_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) :
    sumFour (fun i j k l => (A i j * A k l) * (A i l * A j k)) =
      - matrixFrobSq (A ^ 2) := by
  rw [sumFour_swap_last]
  calc
    _ = sumFour (fun i j k l => -((A i j * A k l) * (A i k * A j l))) := by
      apply sumFour_congr; intro i j k l
      rw [hskew l k]
      ring
    _ = - sumFour (fun i j k l => (A i j * A k l) * (A i k * A j l)) := by
      simp only [sumFour, Finset.sum_neg_distrib]
    _ = _ := by rw [sumFour_cross_one]

theorem sumFour_cross_three {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) :
    sumFour (fun i j k l => (A i k * A j l) * (A i l * A j k)) =
      matrixFrobSq (A ^ 2) := by
  rw [sumFour_swap_middle]
  calc
    _ = sumFour (fun i j k l => -((A i j * A k l) * (A i l * A j k))) := by
      apply sumFour_congr; intro i j k l
      rw [hskew k j]
      ring
    _ = - sumFour (fun i j k l => (A i j * A k l) * (A i l * A j k)) := by
      simp only [sumFour, Finset.sum_neg_distrib]
    _ = _ := by rw [sumFour_cross_two A hskew, neg_neg]

/-- The sum of actual determinants of all ordered four-vertex principal submatrices. -/
def fourDetTotal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sumFour (fun i j k l => (A.submatrix ![i, j, k, l] ![i, j, k, l]).det)

theorem fourDetTotal_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) :
    fourDetTotal A = 3 * matrixFrobSq A ^ 2 - 6 * matrixFrobSq (A ^ 2) := by
  have hterm (i j k l : Fin n) :
      (A.submatrix ![i,j,k,l] ![i,j,k,l]).det =
        A i j ^ 2 * A k l ^ 2 + A i k ^ 2 * A j l ^ 2 + A i l ^ 2 * A j k ^ 2 -
        2 * ((A i j * A k l) * (A i k * A j l)) +
        2 * ((A i j * A k l) * (A i l * A j k)) -
        2 * ((A i k * A j l) * (A i l * A j k)) := by
    rw [det_skew_four (A.submatrix ![i,j,k,l] ![i,j,k,l])
      (fun a b => hskew (![i,j,k,l] a) (![i,j,k,l] b))]
    change (A i j * A k l - A i k * A j l + A i l * A j k) ^ 2 = _
    ring
  unfold fourDetTotal
  simp_rw [hterm]
  have heq : sumFour (fun i j k l =>
      A i j ^ 2 * A k l ^ 2 + A i k ^ 2 * A j l ^ 2 + A i l ^ 2 * A j k ^ 2 -
        2 * ((A i j * A k l) * (A i k * A j l)) +
        2 * ((A i j * A k l) * (A i l * A j k)) -
        2 * ((A i k * A j l) * (A i l * A j k))) =
      sumFour (fun i j k l => A i j ^ 2 * A k l ^ 2) +
      sumFour (fun i j k l => A i k ^ 2 * A j l ^ 2) +
      sumFour (fun i j k l => A i l ^ 2 * A j k ^ 2) -
      2 * sumFour (fun i j k l => (A i j * A k l) * (A i k * A j l)) +
      2 * sumFour (fun i j k l => (A i j * A k l) * (A i l * A j k)) -
      2 * sumFour (fun i j k l => (A i k * A j l) * (A i l * A j k)) := by
    simp only [sumFour, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq, sumFour_mul_sq, sumFour_mul_sq_middle, sumFour_mul_sq_last,
    sumFour_cross_one, sumFour_cross_two A hskew, sumFour_cross_three A hskew]
  ring

end TournamentHamiltonian.Equality
