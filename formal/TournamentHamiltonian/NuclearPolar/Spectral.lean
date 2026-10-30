module

public import TournamentHamiltonian.NuclearPolar.Base

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearPolar
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spectralConj (M : Matrix ι ι ℂ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ (modulus_posSemidef M).isHermitian.eigenvectorUnitary

theorem modulus_spectral (M : Matrix ι ι ℂ) :
    modulus M = spectralConj M (diagonal (fun i => (spectralValues M i : ℂ))) :=
  (modulus_posSemidef M).isHermitian.spectral_theorem

def reciprocal (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  spectralConj M (diagonal (fun i => ((spectralValues M i)⁻¹ : ℂ)))

def supportProjection (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  spectralConj M (diagonal (fun i => if spectralValues M i = 0 then 0 else 1))

theorem reciprocal_isHermitian (M : Matrix ι ι ℂ) : (reciprocal M).IsHermitian := by
  change star (reciprocal M) = reciprocal M
  rw [reciprocal,← map_star]
  congr 1
  simp [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]

theorem reciprocal_mul_modulus (M : Matrix ι ι ℂ) :
    reciprocal M*modulus M = supportProjection M := by
  rw [reciprocal,modulus_spectral,← map_mul,Matrix.diagonal_mul_diagonal,supportProjection]
  congr 1
  congr 1
  ext i
  by_cases h : spectralValues M i = 0
  · simp [h]
  · simp [h,Complex.ofReal_ne_zero.mpr h]

theorem reciprocal_commute (M : Matrix ι ι ℂ) : Commute (reciprocal M) (modulus M) := by
  change reciprocal M*modulus M = modulus M*reciprocal M
  rw [reciprocal,modulus_spectral,← map_mul,← map_mul]
  congr 1
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem supportProjection_mul_modulus (M : Matrix ι ι ℂ) :
    supportProjection M*modulus M = modulus M := by
  rw [supportProjection,modulus_spectral,← map_mul,Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  ext i
  by_cases h : spectralValues M i = 0 <;> simp [h]

theorem reciprocal_mul_modulus_sq (M : Matrix ι ι ℂ) :
    reciprocal M*(modulus M*modulus M) = modulus M := by
  rw [← mul_assoc,reciprocal_mul_modulus,supportProjection_mul_modulus]

theorem supportProjection_norm_le_one (M : Matrix ι ι ℂ) : ‖supportProjection M‖ ≤ 1 := by
  rw [supportProjection,spectralConj,Unitary.conjStarAlgAut_apply,← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro i
  split_ifs <;> norm_num

theorem trace_spectralConj (M A : Matrix ι ι ℂ) : (spectralConj M A).trace = A.trace := by
  rw [spectralConj,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul]
theorem norm_spectralConj (M A : Matrix ι ι ℂ) : ‖spectralConj M A‖ = ‖A‖ := by
  rw [spectralConj,Unitary.conjStarAlgAut_apply,← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]

theorem norm_spectralConj_symm (M A : Matrix ι ι ℂ) : ‖(spectralConj M).symm A‖ = ‖A‖ := by
  rw [← norm_spectralConj M ((spectralConj M).symm A),StarAlgEquiv.apply_symm_apply]
theorem reciprocal_eq_cfc (M : Matrix ι ι ℂ) :
    reciprocal M = cfc (fun x : ℝ => x⁻¹) (modulus M) := by
  rw [(modulus_posSemidef M).isHermitian.cfc_eq]
  simp [reciprocal,spectralConj,Matrix.IsHermitian.cfc,spectralValues,Function.comp_def]

theorem supportProjection_isHermitian (M : Matrix ι ι ℂ) : (supportProjection M).IsHermitian := by
  change star (supportProjection M) = supportProjection M
  rw [supportProjection,← map_star]
  congr 1
  simp only [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  split_ifs <;> simp_all

theorem supportProjection_idempotent (M : Matrix ι ι ℂ) :
    supportProjection M*supportProjection M = supportProjection M := by
  rw [supportProjection,← map_mul,Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  ext i
  split_ifs <;> simp_all
end NuclearPolar
