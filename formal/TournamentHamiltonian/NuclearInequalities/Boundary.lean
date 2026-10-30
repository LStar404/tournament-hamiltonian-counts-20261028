module

public import TournamentHamiltonian.NuclearInequalities.RankOne
public import TournamentHamiltonian.NuclearPolar.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearInequalities
open Matrix NuclearPolar WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem frobeniusNorm_zero : frobeniusNorm (0:Matrix ι ι ℂ) = 0 := by simp [frobeniusNorm]

theorem empty_all_norms (M : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖M‖=0 ∧ frobeniusNorm M=0 ∧ nuclearNorm M=0 := by
  have hM : M=0 := Subsingleton.elim _ _
  rw [hM]
  simp [frobeniusNorm_zero,nuclearNorm_zero]

theorem empty_card_bound (M : Matrix (Fin 0) (Fin 0) ℂ) :
    nuclearNorm M ≤ Real.sqrt 0*frobeniusNorm M := by
  simpa using nuclearNorm_le_sqrt_card_mul_frobeniusNorm M

theorem zero_product_bound (A : Matrix ι ι ℂ) :
    nuclearNorm (A*0)=0 ∧ nuclearNorm ((0:Matrix ι ι ℂ)*A)=0 := by simp [nuclearNorm_zero]

theorem frobeniusNorm_scalar (z : ℂ) : frobeniusNorm (scalarExample z) = ‖z‖ := by
  simp [frobeniusNorm,scalarExample,Real.sqrt_sq (norm_nonneg z)]

theorem scalar_chain_exact (z : ℂ) :
    frobeniusNorm (scalarExample z) = nuclearNorm (scalarExample z) := by
  rw [frobeniusNorm_scalar,nuclearNorm_scalar]

theorem scalar_complex_I :
    nuclearNorm (scalarExample Complex.I)=1 ∧ frobeniusNorm (scalarExample Complex.I)=1 := by
  simp [nuclearNorm_scalar,frobeniusNorm_scalar]

theorem scalar_product_bound (z w : ℂ) :
    nuclearNorm (scalarExample z*scalarExample w) ≤ ‖z‖*‖w‖ := by
  simpa only [frobeniusNorm_scalar] using nuclearNorm_mul_le_frobenius (scalarExample z) (scalarExample w)

theorem nilpotent_frobeniusNorm : frobeniusNorm nilpotentExample = 1 := by
  norm_num [frobeniusNorm,nilpotentExample,Fin.sum_univ_succ]

theorem nilpotent_chain_exact :
    frobeniusNorm nilpotentExample = nuclearNorm nilpotentExample := by
  rw [nilpotent_frobeniusNorm,nilpotent_nuclearNorm]

theorem nilpotent_adjoint_nuclearNorm : nuclearNorm nilpotentExampleᴴ = 1 := by
  rw [nuclearNorm_conjTranspose,nilpotent_nuclearNorm]

theorem nilpotent_product_zero : nuclearNorm (nilpotentExample*nilpotentExample)=0 := by
  have he : nilpotentExample*nilpotentExample=0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [nilpotentExample,Matrix.mul_apply]
  rw [he,nuclearNorm_zero]

theorem repeated_zero_frobenius_sq : frobeniusNorm (diagonal ![(2:ℂ),0,2])^2=8 := by
  rw [frobeniusNorm_sq]
  norm_num [Fin.sum_univ_succ]

theorem repeated_zero_norms :
    nuclearNorm (diagonal ![(2:ℂ),0,2])=4 ∧ frobeniusNorm (diagonal ![(2:ℂ),0,2])=Real.sqrt 8 := by
  refine ⟨repeated_and_zero_spectrum,?_⟩
  rw [← repeated_zero_frobenius_sq,Real.sqrt_sq (frobeniusNorm_nonneg _)]

theorem outer_zero_left (b : EuclideanSpace ℂ ι) : nuclearNorm (outer 0 b)=0 := by
  rw [nuclearNorm_outer,norm_zero,zero_mul]

theorem outer_zero_right (a : EuclideanSpace ℂ ι) : nuclearNorm (outer a 0)=0 := by
  rw [nuclearNorm_outer,norm_zero,mul_zero]

def phaseVector : EuclideanSpace ℂ (Fin 2) := toLp 2 ![1,Complex.I]
def mixedVector : EuclideanSpace ℂ (Fin 2) := toLp 2 ![2,-Complex.I]

theorem phase_outer_entry : outer phaseVector mixedVector 1 1 = -1 := by
  norm_num [outer,phaseVector,mixedVector,Matrix.vecMulVec_apply]

theorem phase_outer_nuclearNorm : nuclearNorm (outer phaseVector mixedVector)=Real.sqrt 10 := by
  have ha : ‖phaseVector‖=Real.sqrt 2 := by
    have hh : ‖phaseVector‖^2=2 := by norm_num [phaseVector,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ]
    rw [← hh,Real.sqrt_sq (norm_nonneg _)]
  have hb : ‖mixedVector‖=Real.sqrt 5 := by
    have hh : ‖mixedVector‖^2=5 := by norm_num [mixedVector,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ]
    rw [← hh,Real.sqrt_sq (norm_nonneg _)]
  rw [nuclearNorm_outer,ha,hb,← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  norm_num
end NuclearInequalities
