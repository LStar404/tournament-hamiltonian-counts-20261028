module

public import TournamentHamiltonian.AccretiveInverse.Coercivity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AccretiveInverse
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invertibility is a conclusion of accretivity, not an input. -/
theorem isUnit_of_accretive (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef) :
    IsUnit M := by
  have h := ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M) (c:=1) (by norm_num)
    (fun x => by simpa using coercive_norm_inner M hM x)
  have hh := h.map (toEuclideanCLM (𝕜:=ℂ) (n:=ι)).symm.toMonoidHom
  simpa using hh

theorem det_ne_zero (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef) : M.det ≠ 0 :=
  (M.isUnit_iff_isUnit_det.mp (isUnit_of_accretive M hM)).ne_zero

theorem inverse_two_sided (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef) :
    M*M⁻¹ = 1 ∧ M⁻¹*M = 1 := by
  have h := M.isUnit_iff_isUnit_det.mp (isUnit_of_accretive M hM)
  exact ⟨M.mul_nonsing_inv h,M.nonsing_inv_mul h⟩

theorem inverse_action_contraction (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef)
    (x : EuclideanSpace ℂ ι) : ‖toEuclideanCLM (𝕜:=ℂ) (n:=ι) M⁻¹ x‖ ≤ ‖x‖ := by
  have h := norm_expansion M hM (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M⁻¹ x)
  have he : toEuclideanCLM (𝕜:=ℂ) (n:=ι) M (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M⁻¹ x) = x := by
    change (toEuclideanCLM (𝕜:=ℂ) (n:=ι) M * toEuclideanCLM (𝕜:=ℂ) (n:=ι) M⁻¹) x = x
    rw [← map_mul,(inverse_two_sided M hM).1,map_one]
    rfl
  simpa only [he] using h

/-- The actual Euclidean operator norm of the genuine nonsingular matrix inverse. -/
theorem inverse_opNorm_le_one (M : Matrix ι ι ℂ) (hM : (hermitianPart M-1).PosSemidef) :
    ‖M⁻¹‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using inverse_action_contraction M hM x

/-- Literal B.6: arbitrary complex square M, Hermitian part at least I, no symmetry or inverse premise. -/
theorem accretive_inverse (M : Matrix ι ι ℂ)
    (hM : (1 : Matrix ι ι ℂ) ≤ (1/2:ℂ) • (M+Mᴴ)) :
    IsUnit M ∧ ‖M⁻¹‖ ≤ 1 := by
  have h : (hermitianPart M-1).PosSemidef := Matrix.le_iff.mp hM
  exact ⟨isUnit_of_accretive M h,inverse_opNorm_le_one M h⟩

/-- Also expose the actual two-sided inverse identities under exactly the manuscript hypothesis. -/
theorem accretive_inverse_identities (M : Matrix ι ι ℂ)
    (hM : (1 : Matrix ι ι ℂ) ≤ (1/2:ℂ) • (M+Mᴴ)) :
    M.det ≠ 0 ∧ M*M⁻¹ = 1 ∧ M⁻¹*M = 1 := by
  have h : (hermitianPart M-1).PosSemidef := Matrix.le_iff.mp hM
  exact ⟨det_ne_zero M h,inverse_two_sided M h⟩
end AccretiveInverse
