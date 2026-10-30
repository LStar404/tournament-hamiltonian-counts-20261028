module

public import TournamentHamiltonian.FiniteDetPerturbation.Real
public import TournamentHamiltonian.AccretiveInverse.Boundary
public import TournamentHamiltonian.NuclearDeterminant.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FiniteDetPerturbation
open Matrix NuclearPolar NuclearInequalities NuclearDeterminant AccretiveInverse
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zero_perturbation_exact (W : Matrix ι ι ℂ) :
    ‖(W+0).det‖=‖W.det‖*Real.exp (nuclearNorm (0:Matrix ι ι ℂ)) := by
  simp [nuclearNorm_zero]

omit [Fintype ι] in
theorem identity_accretive : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (1+(1:Matrix ι ι ℂ)ᴴ) := by
  simp only [Matrix.conjTranspose_one,smul_add,← add_smul]
  norm_num

theorem identity_base (Δ : Matrix ι ι ℂ) :
    ‖(1+Δ).det‖≤Real.exp (nuclearNorm Δ) := by
  simpa using norm_det_add_le_exp_nuclear 1 Δ identity_accretive

theorem empty_complex_exact (W Δ : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖(W+Δ).det‖=‖W.det‖*Real.exp (nuclearNorm Δ) := by
  simp [Matrix.det_isEmpty,nuclearNorm_empty]

theorem complex_scalar_phase (t : ℝ) (Δ : Matrix (Fin 1) (Fin 1) ℂ) :
    ‖(AccretiveInverse.scalarExample t+Δ).det‖ ≤
      ‖(AccretiveInverse.scalarExample t).det‖*Real.exp (nuclearNorm Δ) := by
  apply norm_det_add_le_exp_nuclear
  change 1≤hermitianPart (AccretiveInverse.scalarExample t)
  rw [scalar_hermitianPart]

theorem singular_perturbed_value :
    (AccretiveInverse.scalarExample 0+(-AccretiveInverse.scalarExample 0)).det=0 := by simp

theorem singular_perturbed_bound :
    ‖(AccretiveInverse.scalarExample 0+(-AccretiveInverse.scalarExample 0)).det‖ ≤
      ‖(AccretiveInverse.scalarExample 0).det‖*Real.exp (nuclearNorm (-AccretiveInverse.scalarExample 0)) :=
  complex_scalar_phase 0 _

theorem nonnormal_base (Δ : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖(nonnormalExample+Δ).det‖≤‖nonnormalExample.det‖*Real.exp (nuclearNorm Δ) :=
  norm_det_add_le_exp_nuclear _ _ nonnormal_accretive

theorem empty_real_log (W Δ : Matrix (Fin 0) (Fin 0) ℝ) :
    Real.log (W+Δ).det-Real.log W.det=0 := by simp [Matrix.det_isEmpty]

theorem zero_delta_log (W : Matrix ι ι ℝ) : Real.log (W+0).det-Real.log W.det=0 := by simp

def realNonnormal : Matrix (Fin 2) (Fin 2) ℝ := !![2,2;0,2]

theorem realNonnormal_accretive :
    (1:Matrix (Fin 2) (Fin 2) ℝ) ≤ (1/2:ℝ) • (realNonnormal+realNonnormalᵀ) := by
  rw [Matrix.le_iff]
  have he : (1/2:ℝ) • (realNonnormal+realNonnormalᵀ)-1 =
      (!![1,1;0,0]:Matrix (Fin 2) (Fin 2) ℝ)ᴴ*(!![1,1;0,0]:Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> norm_num [realNonnormal,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem realNonnormal_det : realNonnormal.det=4 := by norm_num [realNonnormal,Matrix.det_fin_two]

theorem realNonnormal_perturbed_det : (realNonnormal+1).det=9 := by
  norm_num [realNonnormal,Matrix.det_fin_two]

theorem realNonnormal_log_bound : Real.log 9-Real.log 4≤2 := by
  have h := real_logdet_add_sub_le_nuclear realNonnormal 1 realNonnormal_accretive
    (by rw [realNonnormal_det]; norm_num) (by rw [realNonnormal_perturbed_det]; norm_num)
  rw [realNonnormal_det,realNonnormal_perturbed_det] at h
  simpa [map_one,nuclearNorm,modulus,CFC.abs_one] using h

theorem singular_log_guard_fails :
    ¬(0<(1+(-1):Matrix (Fin 1) (Fin 1) ℝ).det) := by simp
end FiniteDetPerturbation
