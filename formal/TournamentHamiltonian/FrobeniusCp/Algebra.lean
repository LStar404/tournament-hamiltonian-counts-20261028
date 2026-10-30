module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Basic.Real.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FrobeniusCp
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {𝕜 n : Type*} [CommRing 𝕜] [Fintype n] [DecidableEq n]

def principalMinor (K : Matrix n n 𝕜) (s : Finset n) : 𝕜 :=
  (K.submatrix (Subtype.val : s → n) Subtype.val).det

lemma det_one_add (K : Matrix n n 𝕜) :
    (1 + K).det = ∑ s : Finset n, principalMinor K s := by
  rw [add_comm]
  change Matrix.detRowAlternating ((fun i => K i) + (fun i => (1 : Matrix n n 𝕜) i)) = _
  rw [Matrix.detRowAlternating.map_add_univ]
  exact Finset.sum_congr rfl fun s _ => Matrix.det_piecewise_one_eq_submatrix_det K s

omit [Fintype n] in
@[simp] lemma principalMinor_empty (K : Matrix n n 𝕜) : principalMinor K ∅ = 1 := by
  simp [principalMinor, Matrix.det_isEmpty]

omit [Fintype n] in
@[simp] lemma principalMinor_singleton (K : Matrix n n 𝕜) (i : n) :
    principalMinor K {i} = K i i := by
  let j : ({i} : Finset n) := ⟨i, by simp⟩
  exact Matrix.det_eq_elem_of_subsingleton _ j

lemma low_order_sum (K : Matrix n n 𝕜) :
    (∑ s : Finset n with s.card < 2, principalMinor K s) = 1 + Matrix.trace K := by
  have hset : (Finset.univ.filter fun s : Finset n => s.card < 2) =
      insert ∅ (Finset.univ.image fun i : n => ({i} : Finset n)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · intro h
      have h01 : s.card = 0 ∨ s.card = 1 := by omega
      rcases h01 with h0 | h1
      · exact Or.inl (Finset.card_eq_zero.mp h0)
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
        exact Or.inr ⟨i, hi.symm⟩
    · rintro (rfl | ⟨i, rfl⟩) <;> simp
  rw [hset, Finset.sum_insert (by simp), principalMinor_empty, Finset.sum_image]
  · simp [Matrix.trace, Matrix.diag]
  · intro i _ j _ h
    exact Finset.singleton_injective h

lemma remainder_eq_principal_sum (K : Matrix n n 𝕜) :
    (1 + K).det - 1 - Matrix.trace K =
      ∑ s : Finset n with 2 ≤ s.card, principalMinor K s := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset n))
    (fun s => s.card < 2) (principalMinor K)
  simp only [Nat.not_lt] at h
  rw [low_order_sum, ← det_one_add] at h
  linear_combination -h

def remainderConstant (p : ℕ) : ℝ :=
  ∑ r ∈ (Finset.range (p + 1)).filter (2 ≤ ·), (p.choose r : ℝ) * (r.factorial : ℝ)

lemma remainderConstant_nonneg (p : ℕ) : 0 ≤ remainderConstant p := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq n] in
lemma factorial_subset_sum :
    (∑ s : Finset n with 2 ≤ s.card, (s.card.factorial : ℝ)) =
      remainderConstant (Fintype.card n) := by
  have hu : (Finset.univ : Finset n).powerset = Finset.univ := by ext s; simp
  have h := Finset.sum_powerset_apply_card (fun r => if 2 ≤ r then (r.factorial : ℝ) else 0)
    (x := (Finset.univ : Finset n))
  simpa only [hu, Finset.sum_filter, Finset.card_univ, remainderConstant,
    nsmul_eq_mul, mul_ite, mul_zero] using h

end FrobeniusCp
