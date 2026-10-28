module

public import Tournament.HessianDeterminant
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Push

/-!
# Rationality of the complex determinant in the Hessian formula

The determinant of `I + i C` is rational for every rational skew-symmetric
matrix `C`. This is an exact finite-dimensional statement. No numerical
spectral computation, Pfaffian oracle, or unproved parity lemma is used.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace Tournament.HessianAlgebra

/-- Complex numbers with rational real and imaginary coordinates. -/
noncomputable def rationalComplex : Subring ℂ where
  carrier := {z | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c, ?_⟩
    push_cast
    calc
      _ = (a : ℂ) * c + ((a : ℂ) * d + (b : ℂ) * c) * Complex.I +
          ((b : ℂ) * d) * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_mem_rationalComplex (M : Matrix ι ι ℂ)
    (hM : ∀ i j, M i j ∈ rationalComplex) : M.det ∈ rationalComplex := by
  let N : Matrix ι ι rationalComplex := fun i j => ⟨M i j, hM i j⟩
  have hdet : (N.det : ℂ) = M.det := rationalComplex.subtype.map_det N
  rw [← hdet]
  exact N.det.property

/-- Real matrices are included in complex matrices entry by entry. -/
def complexOfRat (C : Matrix ι ι ℚ) : Matrix ι ι ℂ := fun i j => (C i j : ℂ)

omit [Fintype ι] [DecidableEq ι] in
lemma complexOfRat_skew (C : Matrix ι ι ℚ) (hC : Cᵀ = -C) :
    (complexOfRat C)ᵀ = -complexOfRat C := by
  ext i j
  have h := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [complexOfRat, h]

omit [Fintype ι] in
lemma imaginary_perturbation_hermitian (C : Matrix ι ι ℚ) (hC : Cᵀ = -C) :
    (1 + Complex.I • complexOfRat C).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [complexOfRat, Matrix.one_apply, h, eq_comm]

/-- The complex denominator in the paper is a rational number, not merely real. -/
theorem det_imaginary_perturbation_rational (C : Matrix ι ι ℚ) (hC : Cᵀ = -C) :
    ∃ q : ℚ, (q : ℂ) = (1 + Complex.I • complexOfRat C).det := by
  let M := 1 + Complex.I • complexOfRat C
  have hMmem : ∀ i j, M i j ∈ rationalComplex := by
    intro i j
    refine ⟨(if i = j then 1 else 0), C i j, ?_⟩
    dsimp [M, complexOfRat]
    by_cases hij : i = j <;> simp [Matrix.one_apply, mul_comm, hij]
  obtain ⟨a, b, hab⟩ := det_mem_rationalComplex M hMmem
  have hstar : star M.det = M.det := by
    rw [← Matrix.det_conjTranspose]
    exact congrArg Matrix.det (imaginary_perturbation_hermitian C hC).eq
  have him : M.det.im = 0 := by
    have h := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have hb : (b : ℝ) = 0 := by simpa [hab] using him
  have hbq : b = 0 := by exact_mod_cast hb
  refine ⟨a, ?_⟩
  simpa [hbq] using hab.symm

/-- Rationality of the determinant quotient. Sign/nonzero assertions are separate. -/
theorem determinant_ratio_rational (C : Matrix ι ι ℚ) (hC : Cᵀ = -C) :
    ∃ q : ℚ, (q : ℂ) =
      (1 + complexOfRat C).det / (1 + Complex.I • complexOfRat C).det := by
  obtain ⟨b, hb⟩ := det_imaginary_perturbation_rational C hC
  refine ⟨(1 + C).det / b, ?_⟩
  rw [Rat.cast_div, hb]
  congr 1
  have h := (Rat.castHom ℂ).map_det (1 + C)
  change (Rat.castHom ℂ) (1 + C).det = _
  rw [h]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [complexOfRat, hij]

lemma det_one_sub_square (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (1 - C * C).det = (1 + C).det ^ 2 := by
  have hfactor : 1 - C * C = (1 + C) * (1 - C) := by noncomm_ring
  have htranspose : (1 + C)ᵀ = 1 - C := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hC, sub_eq_add_neg]
  rw [hfactor, Matrix.det_mul, ← htranspose, Matrix.det_transpose, pow_two]

lemma det_one_add_square_complex (C : Matrix ι ι ℂ) (hC : Cᵀ = -C) :
    (1 + C * C).det = (1 + Complex.I • C).det ^ 2 := by
  have hfactor : 1 + C * C = (1 + Complex.I • C) * (1 - Complex.I • C) := by
    rw [mul_sub, add_mul, add_mul]
    simp only [one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, neg_one_smul]
    abel
  have htranspose : (1 + Complex.I • C)ᵀ = 1 - Complex.I • C := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hC, smul_neg,
      sub_eq_add_neg]
  rw [hfactor, Matrix.det_mul, ← htranspose, Matrix.det_transpose, pow_two]

end Tournament.HessianAlgebra
