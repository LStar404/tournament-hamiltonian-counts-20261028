module

public import TournamentHamiltonian.NuclearPolar.Dual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearPolar
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modulus_zero : modulus (0 : Matrix ι ι ℂ) = 0 := CFC.abs_zero

theorem nuclearNorm_zero : nuclearNorm (0 : Matrix ι ι ℂ) = 0 := by simp [nuclearNorm,modulus_zero]

theorem polarFactor_zero : polarFactor (0 : Matrix ι ι ℂ) = 0 := by simp [polarFactor]

theorem reciprocal_zero : reciprocal (0 : Matrix ι ι ℂ) = 0 := by
  rw [reciprocal_eq_cfc,modulus_zero]
  simp

theorem nuclearNorm_empty (M : Matrix (Fin 0) (Fin 0) ℂ) : nuclearNorm M = 0 := by
  simp [nuclearNorm,Matrix.trace]

theorem nuclearNorm_nonneg_diagonal (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    nuclearNorm (diagonal (fun i => (d i : ℂ))) = ∑ i, d i := by
  have hp : (diagonal (fun i => (d i : ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  rw [nuclearNorm,modulus,CFC.abs_of_nonneg _ hp.nonneg,Matrix.trace_diagonal]
  simp

def scalarExample (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := z • 1

theorem nuclearNorm_scalar (z : ℂ) : nuclearNorm (scalarExample z) = ‖z‖ := by
  simp [nuclearNorm,modulus,scalarExample,CFC.abs_smul,Matrix.trace_smul]

theorem nuclearNorm_scalar_I : nuclearNorm (scalarExample Complex.I) = 1 := by
  rw [nuclearNorm_scalar,Complex.norm_I]

def nilpotentExample : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]

theorem nilpotent_det_zero : nilpotentExample.det = 0 := by
  norm_num [nilpotentExample,Matrix.det_fin_two]

theorem nilpotent_ne_zero : nilpotentExample ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [nilpotentExample] at hh

theorem nilpotent_not_normal : nilpotentExample*nilpotentExampleᴴ ≠ nilpotentExampleᴴ*nilpotentExample := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [nilpotentExample,Matrix.mul_apply,Matrix.conjTranspose_apply,map_ofNat] at hh

theorem nilpotent_modulus : modulus nilpotentExample = diagonal ![(0:ℂ),1] := by
  have hd : (diagonal ![(0:ℂ),1]).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  rw [modulus_eq_sqrt]
  apply (CFC.sqrt_eq_iff _ _ (Matrix.posSemidef_conjTranspose_mul_self nilpotentExample).nonneg hd.nonneg).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentExample,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem nilpotent_nuclearNorm : nuclearNorm nilpotentExample = 1 := by
  rw [nuclearNorm,nilpotent_modulus]
  norm_num [Matrix.trace]

theorem nilpotent_totalized_inverse_zero : nilpotentExample⁻¹ = 0 := by
  apply Matrix.nonsing_inv_apply_not_isUnit
  rw [nilpotent_det_zero]
  exact not_isUnit_zero

theorem nilpotent_polar_ne_zero : polarFactor nilpotentExample ≠ 0 := by
  intro h
  have hh := polar_factorization nilpotentExample
  rw [h,zero_mul] at hh
  exact nilpotent_ne_zero hh

theorem nilpotent_polar_ne_totalized_inverse : polarFactor nilpotentExample ≠ nilpotentExample⁻¹ := by
  rw [nilpotent_totalized_inverse_zero]
  exact nilpotent_polar_ne_zero

theorem nilpotent_dual_max :
    IsGreatest ((fun Q : Matrix (Fin 2) (Fin 2) ℂ => ‖(Qᴴ*nilpotentExample).trace‖) '' {Q | ‖Q‖ ≤ 1}) 1 := by
  simpa only [nilpotent_nuclearNorm] using nuclearNorm_dual_max nilpotentExample

theorem repeated_and_zero_spectrum : nuclearNorm (diagonal ![(2:ℂ),0,2]) = 4 := by
  have h := nuclearNorm_nonneg_diagonal ![(2:ℝ),0,2] (by intro i; fin_cases i <;> norm_num)
  have he : (fun i : Fin 3 => ((![2,0,2] i : ℝ) : ℂ)) = ![(2:ℂ),0,2] := by
    ext i
    fin_cases i <;> norm_num
  rw [he] at h
  norm_num [Fin.sum_univ_succ] at h
  exact h
end NuclearPolar
