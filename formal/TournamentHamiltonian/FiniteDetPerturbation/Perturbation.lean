module

public import TournamentHamiltonian.NuclearDeterminant.Perturbation
public import TournamentHamiltonian.AccretiveInverse.Inverse

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FiniteDetPerturbation
open Matrix NuclearPolar NuclearInequalities NuclearDeterminant AccretiveInverse
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuine factorization using the inverse proved to exist from accretivity. -/
theorem accretive_factorization (W Δ : Matrix ι ι ℂ)
    (hW : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (W+Wᴴ)) :
    W+Δ = W*(1+W⁻¹*Δ) := by
  have h := (accretive_inverse_identities W hW).2.1
  rw [mul_add,mul_one,← mul_assoc,h,one_mul]

theorem accretive_det_factorization (W Δ : Matrix ι ι ℂ)
    (hW : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (W+Wᴴ)) :
    (W+Δ).det = W.det*(1+W⁻¹*Δ).det := by
  rw [accretive_factorization W Δ hW,Matrix.det_mul]

theorem nuclearNorm_inverse_mul_le (W Δ : Matrix ι ι ℂ)
    (hW : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (W+Wᴴ)) :
    nuclearNorm (W⁻¹*Δ) ≤ nuclearNorm Δ := by
  exact (nuclearNorm_mul_le_op_left W⁻¹ Δ).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (accretive_inverse W hW).2 (nuclearNorm_nonneg Δ))

/-- Finite determinant perturbation; W+Δ may be singular, and Δ is arbitrary. -/
theorem norm_det_add_le_exp_nuclear (W Δ : Matrix ι ι ℂ)
    (hW : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (W+Wᴴ)) :
    ‖(W+Δ).det‖ ≤ ‖W.det‖*Real.exp (nuclearNorm Δ) := by
  rw [accretive_det_factorization W Δ hW,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg W.det)
  exact (norm_det_one_add_le_exp_nuclearNorm (W⁻¹*Δ)).trans
    (Real.exp_le_exp.mpr (nuclearNorm_inverse_mul_le W Δ hW))

theorem norm_det_add_le_exp_budget (W Δ : Matrix ι ι ℂ)
    (hW : (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (W+Wᴴ)) {B : ℝ} (hΔ : nuclearNorm Δ≤B) :
    ‖(W+Δ).det‖ ≤ ‖W.det‖*Real.exp B :=
  (norm_det_add_le_exp_nuclear W Δ hW).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hΔ) (norm_nonneg W.det))
end FiniteDetPerturbation
