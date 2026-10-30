module

public import TournamentHamiltonian.ComparisonMatrix
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Matrix.Mul

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators

def finPrefix (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < r)

def finPrefixSum {n : ℕ} (x : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ finPrefix n r, x i

def DecreasingNonneg {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ Antitone x

def AbsDom {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), (∑ i ∈ S, |x i|) ≤ finPrefixSum y S.card

def extendFinVec {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then x ⟨i, h⟩ else 0

@[simp] theorem mem_finPrefix {n r : ℕ} (i : Fin n) :
    i ∈ finPrefix n r ↔ i.val < r := by simp [finPrefix]

@[simp] theorem finPrefix_zero (n : ℕ) : finPrefix n 0 = ∅ := by
  ext i
  simp

@[simp] theorem finPrefix_full (n : ℕ) : finPrefix n n = Finset.univ := by
  ext i
  simp

@[simp] theorem finPrefixSum_zero {n : ℕ} (x : Fin n → ℝ) : finPrefixSum x 0 = 0 := by
  simp [finPrefixSum]

@[simp] theorem finPrefixSum_full {n : ℕ} (x : Fin n → ℝ) :
    finPrefixSum x n = ∑ i, x i := by simp [finPrefixSum]

theorem finPrefixSum_eq_range {n : ℕ} (x : Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    finPrefixSum x r = ∑ j ∈ Finset.range r, extendFinVec x j := by
  unfold finPrefixSum
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr ((mem_finPrefix i).mp hi)
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hjr := Finset.mem_range.mp hj
    refine ⟨⟨j, hjr.trans_le hr⟩, ?_, rfl⟩
    exact (mem_finPrefix _).mpr hjr
  · intro i _
    simp [extendFinVec, i.isLt]

theorem sum_fin_eq_range {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, x i) = ∑ j ∈ Finset.range n, extendFinVec x j := by
  simpa only [finPrefixSum_full] using finPrefixSum_eq_range x n le_rfl

theorem finPrefix_card (n r : ℕ) (hr : r ≤ n) : (finPrefix n r).card = r := by
  apply Nat.cast_injective (R := ℝ)
  have h := finPrefixSum_eq_range (fun _ : Fin n => (1 : ℝ)) r hr
  have hs : (∑ j ∈ Finset.range r, extendFinVec (fun _ : Fin n => (1 : ℝ)) j) = r := by
    calc
      _ = ∑ j ∈ Finset.range r, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [extendFinVec, (Finset.mem_range.mp hj).trans_le hr]
      _ = _ := by simp
  simpa only [finPrefixSum, Finset.sum_const, nsmul_eq_mul, mul_one] using h.trans hs

theorem extendFinVec_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∀ j, 0 ≤ extendFinVec x j := by
  intro j
  unfold extendFinVec
  split_ifs
  · exact hx _
  · exact le_rfl

theorem extendFinVec_antitone {n : ℕ} {x : Fin n → ℝ} (hx : Antitone x) :
    AntitoneOn (extendFinVec x) (Set.Iio n) := by
  intro i hi j hj hij
  simp only [Set.mem_Iio] at hi hj
  simpa only [extendFinVec, dif_pos hi, dif_pos hj] using
    hx (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)

/-- Sorting is by the indexed lexicographic API, so repeated absolute values are allowed. -/
theorem sorted_abs_exists {n : ℕ} (x : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), DecreasingNonneg (fun i => |x (π i)|) := by
  let π := Tuple.sort (fun i => -|x i|)
  refine ⟨π, (fun _ => abs_nonneg _), ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -|x i|) hij
  change -|x (π i)| ≤ -|x (π j)| at h
  linarith

theorem finite_dot_le_of_prefix_le {n : ℕ} (u v w : Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) :
    (∑ i, u i * w i) ≤ ∑ i, v i * w i := by
  have hp : ∀ r ≤ n, (∑ j ∈ Finset.range r, extendFinVec u j) ≤
      ∑ j ∈ Finset.range r, extendFinVec v j := by
    intro r hr
    simpa only [finPrefixSum_eq_range u r hr, finPrefixSum_eq_range v r hr] using hprefix r hr
  have h := Finset.sum_mul_le_sum_mul_of_sum_range_le hp
    (extendFinVec_nonneg hw0) (extendFinVec_antitone hw)
  rw [sum_fin_eq_range (fun i => u i * w i), sum_fin_eq_range (fun i => v i * w i)]
  convert h using 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    simp [extendFinVec, Finset.mem_range.mp hj]

theorem finite_sum_sq_le_of_prefix_le {n : ℕ} (u v : Fin n → ℝ)
    (hu : DecreasingNonneg u)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) :
    (∑ i, u i ^ 2) ≤ ∑ i, v i ^ 2 := by
  have hab := finite_dot_le_of_prefix_le u v u hu.1 hu.2 hprefix
  have hs : 0 ≤ ∑ i, (u i - v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have heq : (∑ i, (u i - v i) ^ 2) =
      (∑ i, u i ^ 2) - 2 * (∑ i, v i * u i) + ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [← pow_two] at hab
  rw [heq] at hs
  linarith

theorem absDom_sorted_prefix {n : ℕ} {x y : Fin n → ℝ} (hxy : AbsDom x y)
    (π : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ n) :
    finPrefixSum (fun i => |x (π i)|) r ≤ finPrefixSum y r := by
  classical
  have h := hxy ((finPrefix n r).image π)
  rw [Finset.card_image_of_injective _ π.injective, finPrefix_card n r hr] at h
  rw [Finset.sum_image] at h
  · exact h
  · exact π.injective.injOn

theorem sum_sq_le_of_absDom {n : ℕ} {x y : Fin n → ℝ} (hxy : AbsDom x y) :
    (∑ i, x i ^ 2) ≤ ∑ i, y i ^ 2 := by
  obtain ⟨π, hπ⟩ := sorted_abs_exists x
  have h := finite_sum_sq_le_of_prefix_le (fun i => |x (π i)|) y hπ
    (fun r hr => absDom_sorted_prefix hxy π r hr)
  have heq : (∑ i, |x (π i)| ^ 2) = ∑ i, x i ^ 2 := by
    apply Fintype.sum_equiv π
    intro i
    exact sq_abs (x (π i))
  rwa [heq] at h

end TournamentHamiltonian
