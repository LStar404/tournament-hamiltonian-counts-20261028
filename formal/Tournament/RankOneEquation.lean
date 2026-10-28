module

public import Tournament.HessianBranch
public import Tournament.HessianAlgebra
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Topology.Instances.Matrix

/-!
# Rank-one reduction of the genuine determinant equation

The normalized regular matrix is `P0 d + C`.  The determinant equation in
exponential coordinates reduces exactly to the scalar resolvent equation `phi`.
The identities below are finite-dimensional algebra; no asymptotic or implicit
function assertion is assumed.
-/

@[expose] public section

open Matrix Filter
open scoped Topology
open scoped Matrix

namespace Tournament.RankOneEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one projection onto constants when `d` is the dimension. -/
noncomputable def P0 (d : ℂ) : Matrix ι ι ℂ := fun _ _ => d⁻¹

/-- The exponential diagonal. -/
noncomputable def D (t : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => Complex.exp (t i))

/-- The invertible factor used in the determinant lemma. -/
noncomputable def M (C : Matrix ι ι ℂ) (t : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => Complex.exp (-t i)) - C

/-- The exact scalar equation obtained from the rank-one determinant lemma. -/
noncomputable def phi (d : ℂ) (C : Matrix ι ι ℂ) (t : ι → ℂ) : ℂ :=
  1 - d⁻¹ * ∑ i, ∑ j, (M C t)⁻¹ i j

omit [Fintype ι] in
@[simp] theorem D_zero : D (0 : ι → ℂ) = 1 := by
  simp [D]

omit [Fintype ι] in
@[simp] theorem M_zero (C : Matrix ι ι ℂ) : M C 0 = 1 - C := by
  simp [M]

/-- Exponential coordinates never make the diagonal factor singular. -/
theorem D_det_ne_zero (t : ι → ℂ) : (D t).det ≠ 0 := by
  simp [D, Matrix.det_diagonal, Finset.prod_ne_zero_iff, Complex.exp_ne_zero]

/-- A constant rank-one subtraction, written as a scalar inverse-entry sum. -/
theorem det_sub_P0 (A : Matrix ι ι ℂ) (d : ℂ) (hA : IsUnit A.det) :
    (A - P0 d).det = A.det * (1 - d⁻¹ * ∑ i, ∑ j, A⁻¹ i j) := by
  have hmat : A - P0 d =
      A + Matrix.replicateCol Unit (fun _ : ι => -d⁻¹) *
        Matrix.replicateRow Unit (fun _ : ι => (1 : ℂ)) := by
    ext i j
    simp [P0, Matrix.mul_apply, sub_eq_add_neg]
  rw [hmat, Matrix.det_add_replicateCol_mul_replicateRow hA]
  simp only [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply, one_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp [mul_comm, sub_eq_add_neg]

/-- Matrix factorization underlying the exact scalar equation. -/
theorem matrix_factor (d : ℂ) (C : Matrix ι ι ℂ) (t : ι → ℂ) :
    1 - (P0 d + C) * D t = (M C t - P0 d) * D t := by
  have hdiag : Matrix.diagonal (fun i => Complex.exp (-t i)) * D t = 1 := by
    rw [D, Matrix.diagonal_mul_diagonal]
    simp [← Complex.exp_add]
  unfold M
  rw [Matrix.sub_mul, Matrix.sub_mul, hdiag, Matrix.add_mul]
  abel

/-- Exact determinant reduction; the inverse is used only under invertibility. -/
theorem det_factor (d : ℂ) (C : Matrix ι ι ℂ) (t : ι → ℂ)
    (hM : IsUnit (M C t).det) :
    HessianBranch.K (P0 d + C) (fun i => Complex.exp (t i)) =
      (D t).det * (M C t).det * phi d C t := by
  unfold HessianBranch.K
  change (1 - (P0 d + C) * D t).det = _
  rw [matrix_factor, Matrix.det_mul, det_sub_P0 _ _ hM]
  unfold phi
  ring

/-- Complexification preserves invertibility of `I-C` for real skew matrices. -/
theorem one_sub_complex_skew_isUnit (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    IsUnit (1 - C.map Complex.ofReal) := by
  have h := (HessianAlgebra.one_sub_skew_isUnit C hC).map
    Complex.ofRealHom.mapMatrix
  change IsUnit (Complex.ofRealHom.mapMatrix (1 - C)) at h
  rw [map_sub, map_one] at h
  exact h

/-- The inverse fixes the all-ones column whenever `C` has zero row sums. -/
theorem inv_one_sub_mulVec_one (C : Matrix ι ι ℂ)
    (hC : C *ᵥ (fun _ => 1) = 0) (hA : IsUnit (1 - C).det) :
    (1 - C)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hfix : (1 - C) *ᵥ (fun _ => 1) = fun _ => 1 := by
    simp [Matrix.sub_mulVec, hC]
  calc
    (1 - C)⁻¹ *ᵥ (fun _ => 1) = (1 - C)⁻¹ *ᵥ ((1 - C) *ᵥ (fun _ => 1)) :=
      congrArg _ hfix.symm
    _ = fun _ => 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

/-- The all-ones row is likewise fixed under zero column sums. -/
theorem one_vecMul_inv_one_sub (C : Matrix ι ι ℂ)
    (hC : (fun _ => 1) ᵥ* C = 0) (hA : IsUnit (1 - C).det) :
    (fun _ => 1) ᵥ* (1 - C)⁻¹ = fun _ => 1 := by
  have hfix : (fun _ => 1) ᵥ* (1 - C) = fun _ => 1 := by
    simp [Matrix.vecMul_sub, hC]
  calc
    (fun _ => 1) ᵥ* (1 - C)⁻¹ = ((fun _ => 1) ᵥ* (1 - C)) ᵥ* (1 - C)⁻¹ :=
      congrArg (fun x => x ᵥ* (1 - C)⁻¹) hfix.symm
    _ = fun _ => 1 := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA, Matrix.vecMul_one]

/-- The scalar reduced equation vanishes at the regular base point. -/
theorem phi_zero [Nonempty ι] (C : Matrix ι ι ℂ)
    (hC : C *ᵥ (fun _ => 1) = 0) (hA : IsUnit (1 - C).det) :
    phi (Fintype.card ι) C 0 = 0 := by
  have hrow : ∀ i, ∑ j, (1 - C)⁻¹ i j = 1 := by
    intro i
    have h := congrFun (inv_one_sub_mulVec_one C hC hA) i
    simpa [Matrix.mulVec, dotProduct] using h
  have hd : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [phi, hrow, hd]

/-- In particular the genuine determinant, not an assumed surrogate, is zero. -/
theorem K_one_eq_zero [Nonempty ι] (C : Matrix ι ι ℂ)
    (hC : C *ᵥ (fun _ => 1) = 0) (hA : IsUnit (1 - C).det) :
    HessianBranch.K (P0 (Fintype.card ι) + C) (fun _ => 1) = 0 := by
  have h := det_factor (Fintype.card ι) C 0 (by simpa using hA)
  simpa [phi_zero C hC hA] using h

set_option backward.isDefEq.respectTransparency false in
/-- The full one-coordinate determinant is known exactly at the regular base.
This is a rank-two determinant-lemma computation; no derivatives are assumed. -/
theorem K_update_one [Nonempty ι] (C : Matrix ι ι ℂ) (j : ι) (z : ℂ)
    (hrow : C *ᵥ (fun _ => 1) = 0) (hcol : (fun _ => 1) ᵥ* C = 0)
    (hA : IsUnit (1 - C).det) :
    HessianBranch.K (P0 (Fintype.card ι) + C) (Function.update (fun _ => 1) j z) =
      (1 - C).det * ((1 - z) / (Fintype.card ι : ℂ)) := by
  let d : ℂ := Fintype.card ι
  let A := (1 : Matrix ι ι ℂ) - C
  let N := P0 d + C
  let U : Matrix ι (Fin 2) ℂ := Matrix.of fun i k =>
    if k = 0 then -d⁻¹ else (1 - z) * N i j
  let V : Matrix (Fin 2) ι ℂ := Matrix.of fun k i =>
    if k = 0 then 1 else if i = j then 1 else 0
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmat : 1 - N * Matrix.diagonal (Function.update (fun _ => 1) j z) =
      A + U * V := by
    ext i k
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    by_cases hk : k = j
    · subst k
      simp [A, N, P0, U, V, Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply]
      ring
    · simp [A, N, P0, U, V, Matrix.sub_apply, Matrix.add_apply, hk]
      ring
  have hRrow : ∀ i, ∑ k, A⁻¹ i k = 1 := by
    intro i
    have h := congrFun (inv_one_sub_mulVec_one C hrow hA) i
    simpa [A, Matrix.mulVec, dotProduct] using h
  have hRcol : ∀ k, ∑ i, A⁻¹ i k = 1 := by
    intro k
    have h := congrFun (one_vecMul_inv_one_sub C hcol hA) k
    simpa [A, Matrix.vecMul, dotProduct] using h
  have hNcol : ∀ k, ∑ i, N i k = 1 := by
    intro k
    have h := congrFun hcol k
    simp only [Matrix.vecMul, dotProduct, one_mul, Pi.zero_apply] at h
    simp [N, P0, Finset.sum_add_distrib, h, d, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  have hW00 : (V * A⁻¹ * U) 0 0 = -1 := by
    simp only [Matrix.mul_apply]
    simp only [U, V, Matrix.of_apply, ↓reduceIte, one_mul]
    simp_rw [hRcol]
    simp [d, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]
  have hW01 : (V * A⁻¹ * U) 0 1 = 1 - z := by
    simp only [Matrix.mul_apply]
    simp only [U, V, Matrix.of_apply, ↓reduceIte, one_mul, show (1 : Fin 2) ≠ 0 by decide]
    simp_rw [hRcol, one_mul]
    rw [← Finset.mul_sum, hNcol, mul_one]
  have hW10 : (V * A⁻¹ * U) 1 0 = -d⁻¹ := by
    simp only [Matrix.mul_apply]
    simp only [U, V, Matrix.of_apply, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte]
    rw [← Finset.sum_mul, hRrow, one_mul]
  unfold HessianBranch.K
  change (1 - N * Matrix.diagonal (Function.update (fun _ => 1) j z)).det = _
  rw [hmat, Matrix.det_add_mul U V hA]
  simp only [Matrix.det_fin_two]
  dsimp only [A, d] at hW00 hW01 hW10
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), hW00, hW01, hW10]
  change (1 - C).det * _ = _
  ring

/-- Every eliminated-coordinate derivative is nonzero, with its exact value. -/
theorem K₁_one [Nonempty ι] (C : Matrix ι ι ℂ) (j : ι)
    (hrow : C *ᵥ (fun _ => 1) = 0) (hcol : (fun _ => 1) ᵥ* C = 0)
    (hA : IsUnit (1 - C).det) :
    HessianBranch.K₁ (P0 (Fintype.card ι) + C) j (fun _ => 1) =
      -(1 - C).det / (Fintype.card ι : ℂ) := by
  rw [HessianBranch.K₁_eq_difference, K_update_one C j 1 hrow hcol hA,
    K_update_one C j 0 hrow hcol hA]
  ring

/-- The regular base satisfies the nondegeneracy needed for the actual branch. -/
theorem K₁_one_ne_zero [Nonempty ι] (C : Matrix ι ι ℂ) (j : ι)
    (hrow : C *ᵥ (fun _ => 1) = 0) (hcol : (fun _ => 1) ᵥ* C = 0)
    (hA : IsUnit (1 - C).det) :
    HessianBranch.K₁ (P0 (Fintype.card ι) + C) j (fun _ => 1) ≠ 0 := by
  rw [K₁_one C j hrow hcol hA]
  exact div_ne_zero (neg_ne_zero.mpr hA.ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Exact equivalence with the scalar equation wherever the resolvent exists. -/
theorem K_exp_eq_zero_iff (d : ℂ) (C : Matrix ι ι ℂ) (t : ι → ℂ)
    (hM : IsUnit (M C t).det) :
    HessianBranch.K (P0 d + C) (fun i => Complex.exp (t i)) = 0 ↔
      phi d C t = 0 := by
  rw [det_factor d C t hM]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (D_det_ne_zero t) hM.ne_zero))

/-- The normalized logarithmic branch is analytic without an assumed nonzero coefficient. -/
theorem analyticAt_logBranch [Nonempty ι] (C : Matrix ι ι ℂ) (j : ι)
    (hrow : C *ᵥ (fun _ => 1) = 0) (hcol : (fun _ => 1) ᵥ* C = 0)
    (hA : IsUnit (1 - C).det) :
    AnalyticAt ℂ (HessianBranch.logBranch (P0 (Fintype.card ι) + C) j 1) 0 := by
  exact HessianBranch.analyticAt_logBranch _ j one_ne_zero
    (K₁_one_ne_zero C j hrow hcol hA) (K_one_eq_zero C hrow hA)

omit [Fintype ι] in
/-- The diagonal resolvent matrix depends continuously on the exponential coordinates. -/
theorem continuous_M (C : Matrix ι ι ℂ) : Continuous (M C) := by
  unfold M
  exact (continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_apply i).neg).matrix_diagonal.sub continuous_const

/-- Base invertibility persists in a whole neighborhood, not merely on a formal jet. -/
theorem eventually_isUnit_det_M (C : Matrix ι ι ℂ) (hA : IsUnit (1 - C).det) :
    ∀ᶠ t in 𝓝 (0 : ι → ℂ), IsUnit (M C t).det := by
  have hne : (M C 0).det ≠ 0 := by simpa using hA.ne_zero
  filter_upwards [(continuous_M C).matrix_det.continuousAt.eventually_ne hne] with t ht
  exact isUnit_iff_ne_zero.mpr ht

/-- The actual normalized logarithmic branch satisfies the scalar resolvent equation locally.
The coordinate update inserts the eliminated logarithmic coordinate back into the full vector. -/
theorem logBranch_local_phi_zero [Nonempty ι] (C : Matrix ι ι ℂ) (j : ι)
    (hrow : C *ᵥ (fun _ => 1) = 0) (hcol : (fun _ => 1) ᵥ* C = 0)
    (hA : IsUnit (1 - C).det) :
    ∀ᶠ t in 𝓝 (0 : ι → ℂ),
      phi (Fintype.card ι) C (Function.update t j
        (HessianBranch.logBranch (P0 (Fintype.card ι) + C) j 1 t)) = 0 := by
  let N := P0 (Fintype.card ι) + C
  let L := HessianBranch.logBranch N j 1
  let T : (ι → ℂ) → (ι → ℂ) := fun t => Function.update t j (L t)
  have hn := K₁_one_ne_zero C j hrow hcol hA
  have hz := K_one_eq_zero C hrow hA
  have hL0 : L 0 = 0 := HessianBranch.logBranch_zero N j one_ne_zero hn hz
  have hT0 : T 0 = 0 := by simp [T, hL0]
  have hT : ContinuousAt T 0 :=
    continuousAt_id.update j (analyticAt_logBranch C j hrow hcol hA).continuousAt
  have hMe : ∀ᶠ s in 𝓝 (T 0), IsUnit (M C s).det := by
    rw [hT0]
    exact eventually_isUnit_det_M C hA
  have hM : ∀ᶠ t in 𝓝 (0 : ι → ℂ), IsUnit (M C (T t)).det := hT.eventually hMe
  have hK := HessianBranch.logBranch_local_zero N j one_ne_zero hn hz
  filter_upwards [hM, hK] with t htM htK
  change phi (Fintype.card ι) C (T t) = 0
  apply (K_exp_eq_zero_iff _ C (T t) htM).mp
  have heq : (fun i => Complex.exp (T t i)) =
      Function.update (HessianBranch.expCoordinates 1 t) j (Complex.exp (L t)) := by
    ext i
    by_cases hi : i = j
    · subst i
      simp [T]
    · simp [T, Function.update_of_ne hi, HessianBranch.expCoordinates]
  rw [heq]
  simpa [N, L] using htK

end Tournament.RankOneEquation
