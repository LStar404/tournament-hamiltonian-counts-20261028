module

public import TournamentHamiltonian.NuclearPolar.Dual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearInequalities
open Matrix NuclearPolar
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The existing genuine nuclear norm; the dual formula is a proved characterization. -/
theorem nuclearNorm_le_of_pairing (M : Matrix ι ι ℂ) {b : ℝ}
    (h : ∀ Q : Matrix ι ι ℂ, ‖Q‖ ≤ 1 → ‖(Qᴴ*M).trace‖ ≤ b) :
    nuclearNorm M ≤ b := by
  rw [← polarFactor_attains_trace M]
  exact h _ (polarFactor_norm_le_one M)

theorem nuclearNorm_add_le (M P : Matrix ι ι ℂ) :
    nuclearNorm (M+P) ≤ nuclearNorm M+nuclearNorm P := by
  apply nuclearNorm_le_of_pairing
  intro Q hQ
  rw [Matrix.mul_add,Matrix.trace_add]
  calc
    _ ≤ ‖(Qᴴ*M).trace‖+‖(Qᴴ*P).trace‖ := norm_add_le _ _
    _ ≤ nuclearNorm M+nuclearNorm P := add_le_add
      ((nuclearNorm_dual_max M).2 ⟨Q,hQ,rfl⟩)
      ((nuclearNorm_dual_max P).2 ⟨Q,hQ,rfl⟩)

theorem nuclearNorm_conjTranspose_le (M : Matrix ι ι ℂ) :
    nuclearNorm Mᴴ ≤ nuclearNorm M := by
  apply nuclearNorm_le_of_pairing
  intro Q hQ
  have he : ‖(Qᴴ*Mᴴ).trace‖ = ‖(Q*M).trace‖ := by
    rw [← Matrix.conjTranspose_mul,Matrix.trace_conjTranspose,norm_star,Matrix.trace_mul_comm]
  rw [he]
  simpa only [Matrix.conjTranspose_conjTranspose] using (trace_pairing_le M Qᴴ).trans (by
    simpa [Matrix.l2_opNorm_conjTranspose] using mul_le_mul_of_nonneg_right hQ (nuclearNorm_nonneg M))

theorem nuclearNorm_conjTranspose (M : Matrix ι ι ℂ) :
    nuclearNorm Mᴴ = nuclearNorm M :=
  le_antisymm (nuclearNorm_conjTranspose_le M) (by
    simpa using nuclearNorm_conjTranspose_le Mᴴ)

theorem nuclearNorm_mul_le_op_left (A M : Matrix ι ι ℂ) :
    nuclearNorm (A*M) ≤ ‖A‖*nuclearNorm M := by
  apply nuclearNorm_le_of_pairing
  intro Q hQ
  calc
    _ = ‖((Aᴴ*Q)ᴴ*M).trace‖ := by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ ≤ ‖Aᴴ*Q‖*nuclearNorm M := trace_pairing_le M _
    _ ≤ ‖A‖*nuclearNorm M := by
      apply mul_le_mul_of_nonneg_right _ (nuclearNorm_nonneg M)
      calc
        _ ≤ ‖Aᴴ‖*‖Q‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖A‖*1 := by simpa [Matrix.l2_opNorm_conjTranspose] using mul_le_mul_of_nonneg_left hQ (norm_nonneg A)
        _ = ‖A‖ := mul_one _

theorem nuclearNorm_mul_le_op_right (M A : Matrix ι ι ℂ) :
    nuclearNorm (M*A) ≤ nuclearNorm M*‖A‖ := by
  rw [← nuclearNorm_conjTranspose (M*A),Matrix.conjTranspose_mul]
  simpa [nuclearNorm_conjTranspose,Matrix.l2_opNorm_conjTranspose,mul_comm] using nuclearNorm_mul_le_op_left Aᴴ Mᴴ

theorem trace_mul_le_op_nuclear (A M : Matrix ι ι ℂ) :
    ‖(A*M).trace‖ ≤ ‖A‖*nuclearNorm M := by
  simpa [Matrix.l2_opNorm_conjTranspose] using trace_pairing_le M Aᴴ

theorem opNorm_unitary_le_one (U : unitary (Matrix ι ι ℂ)) : ‖(U:Matrix ι ι ℂ)‖ ≤ 1 := by
  have h := CStarRing.norm_coe_unitary_mul U (1:Matrix ι ι ℂ)
  rw [mul_one] at h
  rw [h]
  rw [show (1:Matrix ι ι ℂ) = diagonal (fun _ => (1:ℂ)) from rfl,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro i; norm_num)

theorem nuclearNorm_unitary_mul (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    nuclearNorm ((U : Matrix ι ι ℂ)*M) = nuclearNorm M := by
  apply le_antisymm
  · exact (nuclearNorm_mul_le_op_left _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (opNorm_unitary_le_one U) (nuclearNorm_nonneg M))
  · calc
      _ = nuclearNorm (((star U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)*((U:Matrix ι ι ℂ)*M)) := by
        rw [← mul_assoc,Unitary.coe_star,Unitary.coe_star_mul_self,one_mul]
      _ ≤ _ := (nuclearNorm_mul_le_op_left _ _).trans (by
        simpa using mul_le_mul_of_nonneg_right (opNorm_unitary_le_one (star U))
          (nuclearNorm_nonneg ((U:Matrix ι ι ℂ)*M)))

theorem nuclearNorm_mul_unitary (M : Matrix ι ι ℂ) (U : unitary (Matrix ι ι ℂ)) :
    nuclearNorm (M*(U : Matrix ι ι ℂ)) = nuclearNorm M := by
  rw [← nuclearNorm_conjTranspose (M*(U:Matrix ι ι ℂ)),Matrix.conjTranspose_mul]
  change nuclearNorm (((star U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)*Mᴴ)=_
  rw [nuclearNorm_unitary_mul,nuclearNorm_conjTranspose]

theorem nuclearNorm_unitary_conjugation (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    nuclearNorm ((U:Matrix ι ι ℂ)*M*((star U:unitary (Matrix ι ι ℂ)):Matrix ι ι ℂ)) = nuclearNorm M := by
  rw [nuclearNorm_mul_unitary,nuclearNorm_unitary_mul]
end NuclearInequalities
