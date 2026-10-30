module

public import TournamentHamiltonian.NuclearPolar.Spectral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearPolar
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The singular-safe polar factor, formed with a spectral pseudoinverse, never M⁻¹. -/
def polarFactor (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := M*reciprocal M

theorem polarFactor_star_mul (M : Matrix ι ι ℂ) : (polarFactor M)ᴴ*M = modulus M := by
  rw [polarFactor,Matrix.conjTranspose_mul,(reciprocal_isHermitian M).eq,mul_assoc,
    ← modulus_sq,reciprocal_mul_modulus_sq]

theorem mul_polarFactor_star (M : Matrix ι ι ℂ) : Mᴴ*polarFactor M = modulus M := by
  have h := congrArg Matrix.conjTranspose (polarFactor_star_mul M)
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    (modulus_posSemidef M).isHermitian.eq] using h

theorem polarFactor_gram (M : Matrix ι ι ℂ) :
    (polarFactor M)ᴴ*polarFactor M = supportProjection M := by
  change (polarFactor M)ᴴ*(M*reciprocal M) = _
  rw [← mul_assoc,polarFactor_star_mul,← (reciprocal_commute M).eq,reciprocal_mul_modulus]

theorem polarFactor_norm_le_one (M : Matrix ι ι ℂ) : ‖polarFactor M‖ ≤ 1 := by
  have h : ‖polarFactor M‖*‖polarFactor M‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,polarFactor_gram]
    exact supportProjection_norm_le_one M
  nlinarith [norm_nonneg (polarFactor M)]

/-- The discarded zero spectral subspace really lies in ker M. -/
theorem polar_residual_gram_zero (M : Matrix ι ι ℂ) :
    (M-polarFactor M*modulus M)ᴴ*(M-polarFactor M*modulus M) = 0 := by
  calc
    _ = Mᴴ*M-(Mᴴ*polarFactor M)*modulus M-modulus M*((polarFactor M)ᴴ*M)+
        modulus M*((polarFactor M)ᴴ*polarFactor M)*modulus M := by
      rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,(modulus_posSemidef M).isHermitian.eq]
      noncomm_ring
    _ = modulus M*modulus M-modulus M*modulus M-modulus M*modulus M+
        modulus M*supportProjection M*modulus M := by
      rw [← modulus_sq,mul_polarFactor_star,polarFactor_star_mul,polarFactor_gram]
    _ = 0 := by
      rw [mul_assoc (modulus M) (supportProjection M),supportProjection_mul_modulus]
      noncomm_ring

theorem polar_factorization (M : Matrix ι ι ℂ) : M = polarFactor M*modulus M := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (M-polarFactor M*modulus M)
  rw [polar_residual_gram_zero,norm_zero] at h
  nlinarith [norm_nonneg (M-polarFactor M*modulus M)]

theorem polarFactor_attains_trace (M : Matrix ι ι ℂ) :
    ‖((polarFactor M)ᴴ*M).trace‖ = nuclearNorm M := by
  rw [polarFactor_star_mul,trace_modulus,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (nuclearNorm_nonneg M)]
end NuclearPolar
