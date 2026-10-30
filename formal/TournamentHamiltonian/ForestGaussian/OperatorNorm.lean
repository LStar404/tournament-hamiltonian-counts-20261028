module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace ForestGaussian

/-- The genuine Euclidean operator norm, not the default entrywise sup norm,
is controlled by a uniform upper bound on a positive semidefinite quadratic form. -/
theorem posSemidef_l2_opNorm_le_of_quadratic_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (hL : L.PosSemidef) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ C * ∑ i, x i ^ 2) :
    ‖L‖ ≤ C := by
  let hM := hL.isHermitian
  have heig (i : ι) : hM.eigenvalues i ≤ C := by
    let v := hM.eigenvectorBasis i
    have hv : (∑ j, v j ^ 2) = 1 := by
      have h := EuclideanSpace.norm_sq_eq v
      rw [hM.eigenvectorBasis.orthonormal.1 i] at h
      simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
    have h := hbound (fun j => v j)
    rw [hv] at h
    have he : hM.eigenvalues i = (fun j => v j) ⬝ᵥ L *ᵥ (fun j => v j) := by
      simpa only [RCLike.re_to_real, Pi.star_apply, star_trivial] using hM.eigenvalues_eq i
    rw [← he, mul_one] at h
    exact h
  rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  change ‖hM.eigenvalues i‖ ≤ C
  rw [Real.norm_eq_abs, abs_of_nonneg (hL.eigenvalues_nonneg i)]
  exact heig i

/-- The constant-four specialization used for finite directed edge sets of degree at most two. -/
theorem posSemidef_l2_opNorm_le_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (hL : L.PosSemidef)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2) :
    ‖L‖ ≤ 4 :=
  posSemidef_l2_opNorm_le_of_quadratic_le L hL 4 (by norm_num) hbound

/-- The same conclusion stated directly as the norm of the induced operator on
`EuclideanSpace ℝ ι`, so the meaning cannot depend on a caller's chosen matrix norm scope. -/
theorem posSemidef_toEuclideanCLM_norm_le_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (hL : L.PosSemidef)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) L‖ ≤ 4 := by
  simpa only [← Matrix.cstar_norm_def] using posSemidef_l2_opNorm_le_four L hL hbound

end ForestGaussian
