module

public import Tournament.HessianAlgebra
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The selected-coordinate and real-angle maps

These maps make the manuscript's coordinate restriction explicit. The eliminated
coordinate is cleared before inserting the implicit branch. The real-angle input
has exactly `n` coordinates, embedded in `n+1` complex coordinates with last entry
zero. Compression then gives `(v₁,…,vₙ,−Σvⱼ)`, precisely the matrix `E` action.
-/

public section

namespace Tournament.HessianCoordinates

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def mass : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, ContinuousLinearMap.proj i

omit [DecidableEq ι] in
@[simp] theorem mass_apply (v : ι → ℂ) : mass v = ∑ i, v i := by
  simp [mass]

@[expose] noncomputable def insert (j : ι) : ℂ →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.single ℂ (fun _ : ι => ℂ) j

omit [Fintype ι] in
@[simp] theorem insert_apply (j : ι) (s : ℂ) : insert j s = Pi.single j s := rfl

@[simp] theorem mass_insert (j : ι) (s : ℂ) : mass (insert j s) = s := by
  simp

@[expose] noncomputable def clear (j : ι) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.id ℂ (ι → ℂ) - (insert j).comp (ContinuousLinearMap.proj j)

omit [Fintype ι] in
@[simp] theorem clear_apply_self (j : ι) (v : ι → ℂ) : clear j v j = 0 := by
  simp [clear]

omit [Fintype ι] in
@[simp] theorem clear_apply_of_ne (j : ι) (v : ι → ℂ) {i : ι} (hi : i ≠ j) :
    clear j v i = v i := by
  simp [clear, Pi.single_eq_of_ne hi]

omit [Fintype ι] in
/-- Clearing the selected coordinate and inserting the branch is exactly update. -/
theorem clear_add_insert (j : ι) (v : ι → ℂ) (s : ℂ) :
    clear j v + insert j s = Function.update v j s := by
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · simp [clear_apply_of_ne j v hi, Function.update_of_ne hi, Pi.single_eq_of_ne hi]

omit [Fintype ι] in
/-- Independence of the eliminated input coordinate is explicit. -/
theorem clear_update (j : ι) (v : ι → ℂ) (s : ℂ) :
    clear j (Function.update v j s) = clear j v := by
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · simp [clear_apply_of_ne j _ hi, Function.update_of_ne hi]

/-- Real `n`-dimensional angle input, embedded with zero last coordinate. -/
@[expose] noncomputable def realIncludeFirst (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    Fin.lastCases 0 (fun j => Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) i

@[simp] theorem realIncludeFirst_castSucc {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    realIncludeFirst n v i.castSucc = (v i : ℂ) := by
  simp [realIncludeFirst]

@[simp] theorem realIncludeFirst_last {n : ℕ} (v : Fin n → ℝ) :
    realIncludeFirst n v (Fin.last n) = 0 := by
  simp [realIncludeFirst]

@[simp] theorem clear_realIncludeFirst {n : ℕ} (v : Fin n → ℝ) :
    clear (Fin.last n) (realIncludeFirst n v) = realIncludeFirst n v := by
  simp [clear]

@[simp] theorem mass_realIncludeFirst {n : ℕ} (v : Fin n → ℝ) :
    mass (realIncludeFirst n v) = ∑ i, (v i : ℂ) := by
  rw [mass_apply, Fin.sum_univ_castSucc]
  simp

/-- The compressed tangent embedding `E`; no selected-coordinate component is
silently available as an independent angle parameter. -/
@[expose] noncomputable def compressedDirection (n : ℕ) (v : Fin n → ℝ) :
    Fin (n + 1) → ℂ :=
  clear (Fin.last n) (realIncludeFirst n v) -
    insert (Fin.last n) (mass (clear (Fin.last n) (realIncludeFirst n v)))

@[simp] theorem compressedDirection_castSucc {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    compressedDirection n v i.castSucc = (v i : ℂ) := by
  simp [compressedDirection]

@[simp] theorem compressedDirection_last {n : ℕ} (v : Fin n → ℝ) :
    compressedDirection n v (Fin.last n) = -∑ i, (v i : ℂ) := by
  simp [compressedDirection, Fin.sum_univ_castSucc]

/-- A matrix as a continuous complex bilinear form (ordinary transpose pairing,
not a Hermitian/conjugate pairing). -/
@[expose] noncomputable def matrixBilinear (Q : Matrix ι ι ℂ) :
    (ι → ℂ) →L[ℂ] (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight
    (∑ j, Q i j • ContinuousLinearMap.proj j)

omit [DecidableEq ι] in
@[simp] theorem matrixBilinear_apply (Q : Matrix ι ι ℂ) (v w : ι → ℂ) :
    matrixBilinear Q v w = v ⬝ᵥ (Q *ᵥ w) := by
  simp [matrixBilinear, Matrix.mulVec, dotProduct, Finset.mul_sum]

/-- On each real coordinate vector, the compressed direction is exactly the
corresponding complexified column of the manuscript's matrix `E`. -/
theorem compressedDirection_basis {n : ℕ} (j : Fin n) :
    compressedDirection n (Pi.single j 1) =
      fun i => (Tournament.HessianAlgebra.differenceEmbedding n i j : ℂ) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [Tournament.HessianAlgebra.differenceEmbedding, Pi.single_apply,
      Ne.symm (Fin.castSucc_ne_last j), apply_ite]
  · simp [Tournament.HessianAlgebra.differenceEmbedding, Pi.single_apply,
      Fin.castSucc_ne_last, eq_comm]

/-- Matrix entries obtained by evaluating the compressed bilinear form. -/
theorem compressed_matrixBilinear_entry {n : ℕ}
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j k : Fin n) :
    matrixBilinear (Q.map Complex.ofReal)
      (compressedDirection n (Pi.single j 1))
      (compressedDirection n (Pi.single k 1)) =
      (((Tournament.HessianAlgebra.differenceEmbedding n)ᵀ * Q *
        Tournament.HessianAlgebra.differenceEmbedding n) j k : ℂ) := by
  rw [compressedDirection_basis, compressedDirection_basis, matrixBilinear_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end Tournament.HessianCoordinates
