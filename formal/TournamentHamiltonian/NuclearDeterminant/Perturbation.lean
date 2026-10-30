module

public import TournamentHamiltonian.NuclearDeterminant.Generating
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearDeterminant
open Matrix NuclearPolar NuclearInequalities
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual polar partial isometry transported into the modulus eigenbasis. -/
def spectralPolarFactor (E : Matrix ι ι ℂ) : Matrix ι ι ℂ := (spectralConj E).symm (polarFactor E)

theorem spectralPolarFactor_norm_le_one (E : Matrix ι ι ℂ) : ‖spectralPolarFactor E‖≤1 := by
  rw [spectralPolarFactor,norm_spectralConj_symm]
  exact polarFactor_norm_le_one E

theorem spectral_polar_reconstruction (E : Matrix ι ι ℂ) :
    spectralConj E (spectralPolarFactor E * diagonal (fun i => (spectralValues E i:ℂ))) = E := by
  rw [map_mul,spectralPolarFactor,StarAlgEquiv.apply_symm_apply,← modulus_spectral,← polar_factorization]

theorem det_one_add_spectral_polar (E : Matrix ι ι ℂ) :
    (1+E).det = (1+spectralPolarFactor E * diagonal (fun i => (spectralValues E i:ℂ))).det := by
  rw [← det_spectralConj E (1+spectralPolarFactor E * diagonal (fun i => (spectralValues E i:ℂ))),
    map_add,map_one,spectral_polar_reconstruction]

/-- The literal product-of-singular-values bound, without normality or invertibility assumptions. -/
theorem norm_det_one_add_le_prod (E : Matrix ι ι ℂ) :
    ‖(1+E).det‖ ≤ ∏ i, (1+spectralValues E i) := by
  rw [det_one_add_spectral_polar]
  exact det_one_add_contraction_diagonal _ (spectralPolarFactor_norm_le_one E) _ (spectralValues_nonneg E)

theorem prod_one_add_spectralValues_le_exp (E : Matrix ι ι ℂ) :
    (∏ i, (1+spectralValues E i)) ≤ Real.exp (nuclearNorm E) := by
  rw [nuclearNorm_eq_sum_spectralValues,Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i _ => add_nonneg zero_le_one (spectralValues_nonneg E i))
  intro i _
  linarith [Real.add_one_le_exp (spectralValues E i)]

/-- B.6 for every complex square matrix, including zero dimension and singular E or I+E. -/
theorem norm_det_one_add_le_exp_nuclearNorm (E : Matrix ι ι ℂ) :
    ‖(1+E).det‖ ≤ Real.exp (nuclearNorm E) :=
  (norm_det_one_add_le_prod E).trans (prod_one_add_spectralValues_le_exp E)
end NuclearDeterminant
