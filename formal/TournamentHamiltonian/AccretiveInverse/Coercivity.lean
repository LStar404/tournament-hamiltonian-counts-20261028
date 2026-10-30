module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AccretiveInverse
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine Hermitian part; the scalar is one half, not a norm bound. -/
def hermitianPart (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1/2:ℂ) • (M+Mᴴ)

omit [Fintype ι] [DecidableEq ι] in
theorem hermitianPart_isHermitian (M : Matrix ι ι ℂ) : (hermitianPart M).IsHermitian := by
  show (hermitianPart M)ᴴ = hermitianPart M
  simp [hermitianPart, add_comm]

/-- Lean's complex inner product is conjugate-linear in its first argument. -/
theorem inner_hermitianPart_re (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) (hermitianPart M) x)).re =
      (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) M x)).re := by
  simp only [hermitianPart, map_smul, map_add, _root_.smul_apply,
    _root_.add_apply, inner_smul_right, inner_add_right,
    ← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [Complex.mul_re]
  have hi := inner_re_symm (𝕜:=ℂ) x (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M x)
  change (inner ℂ x (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M x)).re =
    (inner ℂ (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M x) x).re at hi
  norm_num
  linarith

theorem coercive_inner (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef)
    (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 ≤ (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) M x)).re := by
  have h := hM.re_dotProduct_nonneg (ofLp x)
  have hid : (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) (hermitianPart M-1) x)).re =
      (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) M x)).re-‖x‖^2 := by
    rw [map_sub, map_one]
    simp only [_root_.sub_apply, one_apply_eq_self, inner_sub_right,
      Complex.sub_re, inner_self_eq_norm_sq_to_K]
    rw [inner_hermitianPart_re]
    norm_cast
  have he : (inner ℂ x (toEuclideanCLM (𝕜 := ℂ) (n := ι) (hermitianPart M-1) x)).re =
      RCLike.re (star (ofLp x) ⬝ᵥ ((hermitianPart M-1) *ᵥ ofLp x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    rw [Matrix.ofLp_toEuclideanCLM, dotProduct_comm]
    rfl
  rw [← he,hid] at h
  linarith

theorem coercive_norm_inner (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef)
    (x : EuclideanSpace ℂ ι) :
    ‖x‖^2 ≤ ‖inner ℂ (toEuclideanCLM (𝕜 := ℂ) (n := ι) M x) x‖ := by
  have h := coercive_inner M hM x
  change ‖x‖^2 ≤ RCLike.re (inner ℂ x (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M x)) at h
  rw [inner_re_symm] at h
  exact h.trans (Complex.re_le_norm _)

/-- No invertibility premise: the real-part hypothesis already prevents contraction. -/
theorem antilipschitz (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef) :
    AntilipschitzWith 1 (toEuclideanCLM (𝕜 := ℂ) (n := ι) M) := by
  have h := ContinuousLinearMap.antilipschitz_of_forall_le_inner_map (toEuclideanCLM (𝕜 := ℂ) (n := ι) M)
    (c:=1) (by norm_num) (fun x => by simpa using coercive_norm_inner M hM x)
  simpa using h

theorem norm_expansion (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef)
    (x : EuclideanSpace ℂ ι) : ‖x‖ ≤ ‖toEuclideanCLM (𝕜 := ℂ) (n := ι) M x‖ := by
  have h := (antilipschitz M hM).le_mul_dist x 0
  simpa using h
end AccretiveInverse
