module

public import TournamentHamiltonian.ForestGaussian.Edges

@[expose] public section

set_option autoImplicit false

namespace ForestGaussian
open scoped BigOperators
open Matrix Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {m : ℕ} (F : EdgeSet m)

lemma adjacency_sum_left (x : Fin m → ℝ) :
    (∑ i, ∑ j, if (graph F).Adj i j then x i ^ 2 else 0) =
      ∑ i, ((graph F).degree i : ℝ) * x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [SimpleGraph.degree_eq_sum_if_adj]
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]

lemma adjacency_sum_right (x : Fin m → ℝ) :
    (∑ i, ∑ j, if (graph F).Adj i j then x j ^ 2 else 0) =
      ∑ i, ((graph F).degree i : ℝ) * x i ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [SimpleGraph.adj_comm (graph F)]
  exact adjacency_sum_left F x

/-- A direct finite quadratic bound using actual degree at most two. -/
lemma laplacian_quadratic_le (x : Fin m → ℝ) :
    x ⬝ᵥ (laplacian F *ᵥ x) ≤ 4 * ∑ i, x i ^ 2 := by
  have hbound :
      (∑ i, ∑ j, if (graph F).Adj i j then (x i - x j)^2 else 0) ≤
        4 * ∑ i, ((graph F).degree i : ℝ) * x i ^ 2 := by
    calc
      _ ≤ ∑ i, ∑ j, ((if (graph F).Adj i j then 2 * x i ^ 2 else 0) +
          (if (graph F).Adj i j then 2 * x j ^ 2 else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> nlinarith [sq_nonneg (x i + x j)]
      _ = _ := by
        have hi (p : Prop) (v : ℝ) : (if p then 2*v else 0) = 2*(if p then v else 0) := by
          split_ifs <;> simp
        simp_rw [Finset.sum_add_distrib, hi, ← Finset.mul_sum]
        rw [adjacency_sum_left, adjacency_sum_right]
        ring
  have hdeg : (∑ i, ((graph F).degree i : ℝ) * x i ^ 2) ≤ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast graph_degree_le_two F i) (sq_nonneg _)
  rw [← Matrix.toLinearMap₂'_apply', laplacian, SimpleGraph.lapMatrix_toLinearMap₂']
  linarith

lemma laplacian_entry_sq (i j : Fin m) :
    laplacian F i j ^ 2 =
      (if i = j then ((graph F).degree i : ℝ) ^ 2 else 0) +
        (if (graph F).Adj i j then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    simp [laplacian_diag]
  · by_cases ha : (graph F).Adj i j <;>
      simp [laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, hij, ha]

lemma laplacian_frobenius_sq_eq :
    (∑ i, ∑ j, laplacian F i j ^ 2) =
      ∑ i, (((graph F).degree i : ℝ) ^ 2 + (graph F).degree i) := by
  simp_rw [laplacian_entry_sq, Finset.sum_add_distrib]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    exact (SimpleGraph.degree_eq_sum_if_adj (R := ℝ) (graph F) i).symm

/-- The stronger bound 6a implies both the requested 8a and 8m budgets. -/
lemma laplacian_frobenius_sq_le :
    (∑ i, ∑ j, laplacian F i j ^ 2) ≤ 6 * (edgeCount F : ℝ) := by
  rw [laplacian_frobenius_sq_eq]
  calc
    _ ≤ ∑ i, 3 * ((graph F).degree i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hd : (0 : ℝ) ≤ (graph F).degree i := by positivity
      have hu : ((graph F).degree i : ℝ) ≤ 2 := by exact_mod_cast graph_degree_le_two F i
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, ← Nat.cast_sum, sum_graph_degree]; push_cast; ring

lemma laplacian_frobenius_sq_le_eight_m :
    (∑ i, ∑ j, laplacian F i j ^ 2) ≤ 8 * (m : ℝ) := by
  have ha : (edgeCount F : ℝ) ≤ m := by exact_mod_cast edgeCount_le F
  have hm : (0 : ℝ) ≤ m := by positivity
  exact (laplacian_frobenius_sq_le F).trans (by linarith)

/-- Orthogonality to constants is an actual finite identity of the endpoint vector. -/
lemma imbalance_dot_one : imbalance F ⬝ᵥ (1 : Fin m → ℝ) = 0 := by
  simpa only [dotProduct, Pi.one_apply, mul_one] using sum_imbalance F

end
end ForestGaussian
