module

public import TournamentHamiltonian.NuclearDeterminant.Perturbation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearDeterminant
open Matrix NuclearPolar NuclearInequalities
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zero_endpoint :
    ‖(1+(0:Matrix ι ι ℂ)).det‖ = Real.exp (nuclearNorm (0:Matrix ι ι ℂ)) := by
  simp [nuclearNorm_zero]

theorem empty_endpoint (E : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖(1+E).det‖=1 ∧ Real.exp (nuclearNorm E)=1 := by
  simp [nuclearNorm_empty,Matrix.det_isEmpty]

theorem empty_product (E : Matrix (Fin 0) (Fin 0) ℂ) :
    (∏ i, (1+spectralValues E i)) = 1 := by simp

omit [Fintype ι] in
theorem empty_principal_det (Q : Matrix ι ι ℂ) :
    (Q.submatrix (Subtype.val : (∅:Finset ι) → ι) (Subtype.val : (∅:Finset ι) → ι)).det=1 := by
  simp [Matrix.det_isEmpty]

theorem scalar_det_one_add (z : ℂ) : (1+scalarExample z).det=1+z := by
  simp [scalarExample]

theorem scalar_endpoint (z : ℂ) : ‖1+z‖ ≤ Real.exp ‖z‖ := by
  simpa only [scalar_det_one_add,nuclearNorm_scalar] using norm_det_one_add_le_exp_nuclearNorm (scalarExample z)

theorem singular_shift : (1+scalarExample (-1)).det=0 := by
  rw [scalar_det_one_add]
  norm_num

theorem singular_shift_endpoint : ‖(1+scalarExample (-1)).det‖ ≤ Real.exp 1 := by
  simpa only [nuclearNorm_scalar,norm_neg,norm_one] using norm_det_one_add_le_exp_nuclearNorm (scalarExample (-1))

theorem phase_scalar_det : (1+scalarExample Complex.I).det=1+Complex.I := scalar_det_one_add _

theorem phase_scalar_modulus_sq : ‖(1+scalarExample Complex.I).det‖^2=2 := by
  rw [phase_scalar_det,← Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply]

theorem nilpotent_shift_det : (1+nilpotentExample).det=1 := by
  norm_num [nilpotentExample,Matrix.det_fin_two]

theorem nilpotent_endpoint : ‖(1+nilpotentExample).det‖ ≤ Real.exp 1 := by
  simpa only [nilpotent_nuclearNorm] using norm_det_one_add_le_exp_nuclearNorm nilpotentExample

theorem repeated_zero_shift_det : (1+diagonal ![(2:ℂ),0,2]).det=9 := by
  rw [← Matrix.diagonal_one,Matrix.diagonal_add,Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

theorem repeated_zero_endpoint :
    ‖(1+diagonal ![(2:ℂ),0,2]).det‖ ≤ Real.exp 4 := by
  simpa only [repeated_and_zero_spectrum] using norm_det_one_add_le_exp_nuclearNorm (diagonal ![(2:ℂ),0,2])

theorem diagonal_nonneg_shift_norm (s : ι → ℝ) (hs : ∀ i,0≤s i) :
    ‖(1+diagonal (fun i => (s i:ℂ))).det‖=∏ i,(1+s i) := by
  rw [← Matrix.diagonal_one,Matrix.diagonal_add,Matrix.det_diagonal,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  change ‖(1:ℂ)+(s i:ℂ)‖=1+s i
  rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg zero_le_one (hs i))]
end NuclearDeterminant
