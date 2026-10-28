module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Algebraic core of the Wormald Hessian formula

This file proves general matrix statements. It does NOT define the analytic angle
function, or assert that its second derivative is the matrix studied here.
The analytic identification is a separate obligation.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace Tournament.HessianAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared Frobenius norm, expressed without choosing a matrix norm instance. -/
def frobeniusSq (C : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, C i j ^ 2

/-- The rational matrix expression appearing in the paper's Hessian formula. -/
noncomputable def resolvent (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 + C * C) * (1 - C * C)⁻¹

omit [DecidableEq ι] in
lemma dot_mulVec_sq_le_frobenius (C : Matrix ι ι ℝ) (x : ι → ℝ) :
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) ≤ frobeniusSq C * (x ⬝ᵥ x) := by
  calc
    (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = ∑ i, (∑ j, C i j * x j) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, pow_two]
    _ ≤ ∑ i, (∑ j, C i j ^ 2) * (∑ j, x j ^ 2) :=
      Finset.sum_le_sum fun i _ =>
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (C i) x
    _ = frobeniusSq C * (x ⬝ᵥ x) := by
      simp only [frobeniusSq, dotProduct, pow_two, Finset.sum_mul]

omit [DecidableEq ι] in
lemma skew_quadratic_zero (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) (x : ι → ℝ) :
    x ⬝ᵥ (C *ᵥ x) = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec C x x
  rw [hC, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

omit [DecidableEq ι] in
lemma skew_square_quadratic (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) (x : ι → ℝ) :
    x ⬝ᵥ ((C * C) *ᵥ x) = -((C *ᵥ x) ⬝ᵥ (C *ᵥ x)) := by
  have h := Matrix.dotProduct_transpose_mulVec C x (C *ᵥ x)
  rw [hC, Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_mulVec] at h
  linarith

lemma one_sub_skew_isUnit (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    IsUnit (1 - C) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply dotProduct_self_eq_zero.mp
  have hz : (1 - C) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h := congrArg (fun v => (x - y) ⬝ᵥ v) hz
  simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    skew_quadratic_zero C hC, sub_zero, dotProduct_zero] using h

lemma one_sub_square_posDef (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (1 - C * C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (1 - C * C)ᵀ = 1 - C * C
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hC, neg_mul_neg]
  · intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hx : 0 < star x ⬝ᵥ x)
    have hnonneg : 0 ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by
      simpa using dotProduct_star_self_nonneg (C *ᵥ x)
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
      skew_square_quadratic C hC]
    linarith

lemma one_add_square_posDef (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : (1 + C * C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (1 + C * C)ᵀ = 1 + C * C
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hC, neg_mul_neg]
  · intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hx : 0 < star x ⬝ᵥ x)
    have hbound := dot_mulVec_sq_le_frobenius C x
    have hstrict : frobeniusSq C * (x ⬝ᵥ x) < x ⬝ᵥ x := by
      simpa using mul_lt_mul_of_pos_right hF hxpos
    simp only [star_trivial, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
      skew_square_quadratic C hC]
    linarith

/-- Congruence representation; all inverses are justified by invertibility lemmas. -/
theorem resolvent_eq_congruence (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    resolvent C = (1 - C)⁻¹ᵀ * (1 + C * C) * (1 - C)⁻¹ := by
  let B := 1 - C
  let U := B⁻¹
  let A := 1 + C * C
  let D := 1 - C * C
  have hB : IsUnit B := one_sub_skew_isUnit C hC
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hD : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp
    (one_sub_square_posDef C hC).isUnit
  have hUB : U * B = 1 := Matrix.nonsing_inv_mul B hBd
  have hBU : B * U = 1 := Matrix.mul_nonsing_inv B hBd
  have hUBt : Uᵀ * Bᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBU
  have hBt : Bᵀ = 1 + C := by
    dsimp [B]
    rw [Matrix.transpose_sub, Matrix.transpose_one, hC, sub_neg_eq_add]
  have hfactor : D = B * Bᵀ := by
    rw [hBt]
    dsimp [B, D]
    noncomm_ring
  have hcomm : A * Bᵀ = Bᵀ * A := by
    rw [hBt]
    dsimp [A]
    noncomm_ring
  have hprod : (Uᵀ * A * U) * D = A := by
    calc
      (Uᵀ * A * U) * D = (Uᵀ * A) * (U * B) * Bᵀ := by
        rw [hfactor]
        simp only [Matrix.mul_assoc]
      _ = Uᵀ * (A * Bᵀ) := by rw [hUB]; simp only [mul_one, Matrix.mul_assoc]
      _ = Uᵀ * (Bᵀ * A) := by rw [hcomm]
      _ = A := by rw [← Matrix.mul_assoc, hUBt, one_mul]
  change A * D⁻¹ = Uᵀ * A * U
  calc
    A * D⁻¹ = ((Uᵀ * A * U) * D) * D⁻¹ := by rw [hprod]
    _ = Uᵀ * A * U := Matrix.mul_nonsing_inv_cancel_right D _ hD

/-- The symmetric resolvent identity used by the scalar two-jet calculation. -/
theorem resolvent_eq_inverse_add_transpose_sub_one (C : Matrix ι ι ℝ)
    (hC : Cᵀ = -C) :
    resolvent C = (1 - C)⁻¹ + (1 - C)⁻¹ᵀ - 1 := by
  let B := 1 - C
  let U := B⁻¹
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp
    (one_sub_skew_isUnit C hC)
  have hBU : B * U = 1 := Matrix.mul_nonsing_inv B hBd
  have hUtBt : Uᵀ * Bᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hBU
  have hBt : Bᵀ = 1 + C := by
    dsimp [B]
    rw [Matrix.transpose_sub, Matrix.transpose_one, hC, sub_neg_eq_add]
  have hA : 1 + C * C = Bᵀ + B - Bᵀ * B := by
    rw [hBt]
    dsimp [B]
    noncomm_ring
  rw [resolvent_eq_congruence C hC]
  change Uᵀ * (1 + C * C) * U = U + Uᵀ - 1
  rw [hA, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul]
  rw [hUtBt, one_mul, Matrix.mul_assoc Uᵀ B U, hBU, mul_one,
    ← Matrix.mul_assoc Uᵀ Bᵀ B, hUtBt, one_mul, hBU]

/-- Casting an invertible matrix preserves its (totalized) matrix inverse. -/
theorem map_inverse_of_isUnit {R K : Type*} [Field R] [Field K]
    (f : R →+* K) (M : Matrix ι ι R) (hM : IsUnit M) :
    f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).mp hM), map_one]

/-- Complexification of the exact real symmetric-resolvent identity. The
transpose here is ordinary transpose, as required for the holomorphic two-jet. -/
theorem complexified_resolvent_identity (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (1 - C.map Complex.ofReal)⁻¹ + (1 - C.map Complex.ofReal)⁻¹ᵀ - 1 =
      (resolvent C).map Complex.ofReal := by
  have hB : Complex.ofRealHom.mapMatrix (1 - C) = 1 - C.map Complex.ofReal := by
    rw [map_sub, map_one]
    rfl
  have hi := map_inverse_of_isUnit Complex.ofRealHom (1 - C) (one_sub_skew_isUnit C hC)
  rw [hB] at hi
  have hit : Complex.ofRealHom.mapMatrix ((1 - C)⁻¹ᵀ) =
      (1 - C.map Complex.ofReal)⁻¹ᵀ := by
    change (Complex.ofRealHom.mapMatrix ((1 - C)⁻¹))ᵀ = _
    rw [hi]
  have h := congrArg Complex.ofRealHom.mapMatrix
    (resolvent_eq_inverse_add_transpose_sub_one C hC)
  rw [map_sub, map_add, map_one, hi, hit] at h
  exact h.symm

/-- General positive definiteness of the full matrix expression. -/
theorem resolvent_posDef (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : (resolvent C).PosDef := by
  rw [resolvent_eq_congruence C hC]
  have hU : Function.Injective ((1 - C)⁻¹ : Matrix ι ι ℝ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.isUnit_nonsing_inv_iff.mpr (one_sub_skew_isUnit C hC))
  simpa using (one_add_square_posDef C hC hF).conjTranspose_mul_mul_same hU

/-- Column `j` is `e_j - e_last`, without a choice of orthonormal basis. -/
def differenceEmbedding (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => (if i = j.castSucc then 1 else 0) - (if i = Fin.last n then 1 else 0)

@[simp] lemma differenceEmbedding_mulVec_castSucc (n : ℕ) (v : Fin n → ℝ) (j : Fin n) :
    (differenceEmbedding n *ᵥ v) j.castSucc = v j := by
  simp [differenceEmbedding, Matrix.mulVec, dotProduct, Fin.castSucc_ne_last]

lemma differenceEmbedding_injective (n : ℕ) :
    Function.Injective (differenceEmbedding n).mulVec := by
  intro v w h
  funext j
  have := congrFun h j.castSucc
  simpa using this

/-- The paper's compressed algebraic Hessian, not yet an analytic derivative. -/
noncomputable def compressedResolvent (n : ℕ) (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (differenceEmbedding n)ᵀ * resolvent C * differenceEmbedding n

/-- Uniform in the size and entries of the skew matrix. -/
theorem compressedResolvent_posDef (n : ℕ)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : (compressedResolvent n C).PosDef := by
  simpa [compressedResolvent] using
    (resolvent_posDef C hC hF).conjTranspose_mul_mul_same (differenceEmbedding_injective n)

/-- Nondegeneracy of the algebraic candidate, conditional only on skewness and
an explicit Frobenius bound, not on the desired determinant conclusion. -/
theorem compressedResolvent_det_pos (n : ℕ)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : 0 < (compressedResolvent n C).det :=
  (compressedResolvent_posDef n C hC hF).det_pos

/-- Exact Frobenius sum for any normalized tournament sign matrix.  No regularity
or particular graph is assumed. -/
theorem normalizedSign_frobeniusSq (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hdiag : ∀ i, S i i = 0)
    (hoff : ∀ i j, i ≠ j → S i j ^ 2 = 1) :
    frobeniusSq ((d : ℝ)⁻¹ • S) = ((d : ℝ) - 1) / d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hentry (i j : Fin d) :
      (((d : ℝ)⁻¹ • S) i j) ^ 2 =
        if i = j then 0 else ((d : ℝ)⁻¹) ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [Matrix.smul_apply, mul_pow, hoff i j hij, hij]
  have hrow (i : Fin d) :
      (∑ j : Fin d, if i = j then (0 : ℝ) else ((d : ℝ)⁻¹) ^ 2) =
        (d : ℝ) * ((d : ℝ)⁻¹) ^ 2 - ((d : ℝ)⁻¹) ^ 2 := by
    calc
      _ = ∑ j : Fin d, (((d : ℝ)⁻¹) ^ 2 -
          if j = i then ((d : ℝ)⁻¹) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp_all [eq_comm]
      _ = _ := by simp [Finset.sum_sub_distrib]
  unfold frobeniusSq
  simp_rw [hentry, hrow]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The normalization of tournament signs supplies the strict bound, rather than
requiring the user to postulate it. -/
theorem normalizedSign_frobeniusSq_lt_one (d : ℕ) (hd : 0 < d)
    (S : Matrix (Fin d) (Fin d) ℝ) (hdiag : ∀ i, S i i = 0)
    (hoff : ∀ i j, i ≠ j → S i j ^ 2 = 1) :
    frobeniusSq ((d : ℝ)⁻¹ • S) < 1 := by
  rw [normalizedSign_frobeniusSq d hd S hdiag hoff]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_lt_iff₀ hdR).mpr
  linarith

/-- General sign-matrix corollary: the algebraic Hessian is positive definite
for every tournament size, not merely for enumerated small examples. -/
theorem tournament_compressed_posDef (n : ℕ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : Sᵀ = -S)
    (hdiag : ∀ i, S i i = 0) (hoff : ∀ i j, i ≠ j → S i j ^ 2 = 1) :
    (compressedResolvent n (((n + 1 : ℕ) : ℝ)⁻¹ • S)).PosDef := by
  apply compressedResolvent_posDef
  · simp only [Matrix.transpose_smul, hS, smul_neg]
  · exact normalizedSign_frobeniusSq_lt_one (n + 1) (Nat.zero_lt_succ n) S hdiag hoff

end Tournament.HessianAlgebra
