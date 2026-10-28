module

public import Tournament.HessianAlgebra
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Positivity

/-!
# Determinant of the compressed Hessian candidate

These are matrix identities; the analytic angle-function identification is not
assumed or claimed.  The determinant factor is proved using an explicit splitting
of the constant direction, rather than an unproved restriction-determinant rule.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace Tournament.HessianAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma resolvent_det (C : Matrix ι ι ℝ) :
    (resolvent C).det = (1 + C * C).det / (1 - C * C).det := by
  simp [resolvent, Matrix.det_mul, Matrix.det_nonsing_inv, div_eq_mul_inv]

lemma resolvent_mulVec_of_mulVec_zero (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (x : ι → ℝ) (hx : C *ᵥ x = 0) : resolvent C *ᵥ x = x := by
  have hD : IsUnit (1 - C * C).det := (Matrix.isUnit_iff_isUnit_det _).mp
    (one_sub_square_posDef C hC).isUnit
  have hDx : (1 - C * C) *ᵥ x = x := by
    simp [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx]
  have hUx : (1 - C * C)⁻¹ *ᵥ x = x := by
    calc
      _ = (1 - C * C)⁻¹ *ᵥ ((1 - C * C) *ᵥ x) := by rw [hDx]
      _ = x := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hD, Matrix.one_mulVec]
  simp [resolvent, ← Matrix.mulVec_mulVec, hUx, Matrix.add_mulVec, hx]

/-- A split compression preserves the determinant except for its Gram factor. -/
theorem det_compression_of_split {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : Matrix ι κ ℝ) (F : Matrix κ ι ℝ) (P Q : Matrix ι ι ℝ)
    (hFE : F * E = 1) (hEF : E * F = 1 - P)
    (hEP : Eᵀ * P = 0) (hQP : Q * P = P) :
    (Eᵀ * Q * E).det = (Eᵀ * E).det * Q.det := by
  have hleft : (Eᵀ * E) * F = Eᵀ := by
    rw [Matrix.mul_assoc, hEF, Matrix.mul_sub, Matrix.mul_one, hEP, sub_zero]
  have hsplit : F * Q * E = 1 + F * ((Q - 1) * E) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hFE]
    abel
  have hdet : (F * Q * E).det = Q.det := by
    rw [hsplit, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hEF]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hQP, sub_self,
      sub_zero]
    abel
  calc
    (Eᵀ * Q * E).det = ((Eᵀ * E) * (F * Q * E)).det := by
      congr 1
      simp only [← Matrix.mul_assoc, hleft]
    _ = (Eᵀ * E).det * (F * Q * E).det := Matrix.det_mul _ _
    _ = (Eᵀ * E).det * Q.det := by rw [hdet]

@[simp] lemma last_ne_castSucc {n : ℕ} (j : Fin n) : Fin.last n ≠ j.castSucc :=
  (Fin.castSucc_ne_last j).symm

/-- Projection onto the all-one direction. -/
noncomputable def constantProjection (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun _ _ => ((n + 1 : ℕ) : ℝ)⁻¹

/-- Left inverse of `differenceEmbedding`, killing the all-one direction. -/
noncomputable def differenceLeftInverse (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℝ :=
  fun j i => (if i = j.castSucc then 1 else 0) - ((n + 1 : ℕ) : ℝ)⁻¹

lemma differenceLeftInverse_mul_embedding (n : ℕ) :
    differenceLeftInverse n * differenceEmbedding n = 1 := by
  ext j k
  simp [Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, differenceLeftInverse,
    differenceEmbedding, Fin.castSucc_ne_last, eq_comm]

lemma embedding_mul_differenceLeftInverse (n : ℕ) :
    differenceEmbedding n * differenceLeftInverse n = 1 - constantProjection n := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  ext i k
  refine Fin.lastCases ?_ (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun l => ?_) k
    · simp [Matrix.mul_apply, differenceEmbedding, differenceLeftInverse,
        constantProjection, last_ne_castSucc]
      field_simp
      ring
    · simp [Matrix.mul_apply, differenceEmbedding, differenceLeftInverse,
        constantProjection, last_ne_castSucc,
        Finset.sum_sub_distrib]
      field_simp
      ring
  · simp [Matrix.one_apply, Matrix.mul_apply, differenceEmbedding, differenceLeftInverse,
      constantProjection, Fin.castSucc_ne_last]
    by_cases h : k = j.castSucc <;> simp_all [eq_comm]

lemma embedding_transpose_mul_projection (n : ℕ) :
    (differenceEmbedding n)ᵀ * constantProjection n = 0 := by
  ext j k
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, differenceEmbedding,
    constantProjection, Fin.castSucc_ne_last, last_ne_castSucc]

lemma embedding_gram (n : ℕ) :
    (differenceEmbedding n)ᵀ * differenceEmbedding n =
      (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of (fun _ _ => 1) := by
  ext j k
  simp [Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, differenceEmbedding,
    Fin.castSucc_ne_last, eq_comm]

lemma embedding_gram_det (n : ℕ) :
    ((differenceEmbedding n)ᵀ * differenceEmbedding n).det = ((n + 1 : ℕ) : ℝ) := by
  rw [embedding_gram]
  have hJ : (Matrix.of (fun _ _ => 1) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.replicateCol Unit (fun _ : Fin n => (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hJ, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Nat.cast_add, add_comm]

lemma mul_constantProjection (n : ℕ) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1)) : Q * constantProjection n = constantProjection n := by
  ext i j
  have h := congrFun hQ i
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  simp only [Matrix.mul_apply, constantProjection, ← Finset.sum_mul, h, one_mul]

/-- The dimension factor in the manuscript's compressed determinant, with only
constant-direction invariance assumed. Symmetry is not needed for this identity. -/
theorem det_compression (n : ℕ) (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hQ : Q *ᵥ (fun _ => 1) = (fun _ => 1)) :
    ((differenceEmbedding n)ᵀ * Q * differenceEmbedding n).det =
      ((n + 1 : ℕ) : ℝ) * Q.det := by
  rw [det_compression_of_split (differenceEmbedding n) (differenceLeftInverse n)
    (constantProjection n) Q (differenceLeftInverse_mul_embedding n)
    (embedding_mul_differenceLeftInverse n) (embedding_transpose_mul_projection n)
    (mul_constantProjection n Q hQ), embedding_gram_det]

/-- The full compressed determinant identity of §3.7, for every zero-row-sum
skew matrix. Positivity is separately proved in `HessianAlgebra`. -/
theorem compressedResolvent_det (n : ℕ)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : Cᵀ = -C)
    (hzero : C *ᵥ (fun _ => 1) = 0) :
    (compressedResolvent n C).det = ((n + 1 : ℕ) : ℝ) *
      (1 + C * C).det / (1 - C * C).det := by
  unfold compressedResolvent
  rw [det_compression n (resolvent C) (resolvent_mulVec_of_mulVec_zero C hC _ hzero),
    resolvent_det]
  ring

end Tournament.HessianAlgebra
