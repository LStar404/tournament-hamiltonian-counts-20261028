module

public import TournamentHamiltonian.AccretiveInverse.Inverse

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AccretiveInverse
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def scalarExample (t : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => 1+Complex.I*(t:ℂ)

theorem scalar_hermitianPart (t : ℝ) : hermitianPart (scalarExample t) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [hermitianPart, scalarExample, Matrix.conjTranspose_apply]
  ring

theorem scalar_inverse_bound (t : ℝ) : IsUnit (scalarExample t) ∧ ‖(scalarExample t)⁻¹‖ ≤ 1 := by
  apply accretive_inverse
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤ hermitianPart (scalarExample t)
  rw [scalar_hermitianPart]

theorem scalar_inverse_entry (t : ℝ) :
    (scalarExample t)⁻¹ 0 0 = (1+Complex.I*(t:ℂ))⁻¹ := by
  have hz : (1+Complex.I*(t:ℂ)) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have he : (scalarExample t)⁻¹ = (fun _ _ => (1+Complex.I*(t:ℂ))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarExample,Matrix.mul_apply,hz]
  rw [he]

theorem scalar_sharp_at_zero : ‖(scalarExample 0)⁻¹‖ = 1 := by
  have h : scalarExample 0 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarExample]
  rw [h]
  simp

theorem empty_matrix_boundary (M : Matrix (Fin 0) (Fin 0) ℂ) :
    IsUnit M ∧ M.det = 1 ∧ ‖M⁻¹‖ = 0 := by
  have h : hermitianPart M = 1 := Subsingleton.elim _ _
  have hp : (hermitianPart M-1).PosSemidef := by rw [h,sub_self]; exact Matrix.PosSemidef.zero
  refine ⟨isUnit_of_accretive M hp,?_,norm_of_subsingleton _⟩
  simp

/-- A genuinely nonnormal square example satisfying the semidefinite boundary hypothesis. -/
def nonnormalExample : Matrix (Fin 2) (Fin 2) ℂ := !![2,2;0,2]
def gramWitness : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;0,0]

theorem nonnormal_hermitianPart_gram :
    hermitianPart nonnormalExample-1 = gramWitnessᴴ*gramWitness := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hermitianPart,nonnormalExample,gramWitness,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem nonnormal_accretive : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤ hermitianPart nonnormalExample := by
  rw [Matrix.le_iff,nonnormal_hermitianPart_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem nonnormal_not_normal : nonnormalExample*nonnormalExampleᴴ ≠ nonnormalExampleᴴ*nonnormalExample := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [nonnormalExample,Matrix.mul_apply,Matrix.conjTranspose_apply, map_ofNat] at hh

theorem nonnormal_inverse_exact : nonnormalExample⁻¹ = !![(1/2:ℂ),-1/2;0,1/2] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [nonnormalExample,Matrix.mul_apply]

theorem nonnormal_inverse_bound : IsUnit nonnormalExample ∧ ‖nonnormalExample⁻¹‖ ≤ 1 :=
  accretive_inverse nonnormalExample nonnormal_accretive
end AccretiveInverse
