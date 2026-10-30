module

public import TournamentHamiltonian.NuclearInequalities.Frobenius

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearInequalities
open Matrix NuclearPolar WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def column (M : Matrix ι ι ℂ) (j : ι) : EuclideanSpace ℂ ι := toLp 2 (fun i => M i j)

omit [DecidableEq ι] in
theorem frobeniusNorm_sq_eq_sum_column (M : Matrix ι ι ℂ) :
    frobeniusNorm M^2 = ∑ j, ‖column M j‖^2 := by
  rw [frobeniusNorm_sq]
  simp only [column,PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_comm

theorem column_mul (A B : Matrix ι ι ℂ) (j : ι) :
    column (A*B) j = toEuclideanCLM (𝕜:=ℂ) (n:=ι) A (column B j) := by
  ext i
  rfl

theorem frobeniusNorm_mul_le_op_left (A B : Matrix ι ι ℂ) :
    frobeniusNorm (A*B) ≤ ‖A‖*frobeniusNorm B := by
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg A) (frobeniusNorm_nonneg B))
  rw [mul_pow,frobeniusNorm_sq_eq_sum_column,frobeniusNorm_sq_eq_sum_column,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [column_mul,← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
    (toEuclideanCLM (𝕜:=ℂ) (n:=ι) A).le_opNorm (column B j)

theorem frobeniusNorm_mul_le_op_right (A B : Matrix ι ι ℂ) :
    frobeniusNorm (A*B) ≤ frobeniusNorm A*‖B‖ := by
  rw [← frobeniusNorm_conjTranspose (A*B),Matrix.conjTranspose_mul]
  simpa [frobeniusNorm_conjTranspose,Matrix.l2_opNorm_conjTranspose,mul_comm] using
    frobeniusNorm_mul_le_op_left Bᴴ Aᴴ

/-- Schatten Hölder bound from the actual dual attainer and entrywise Hilbert Cauchy–Schwarz. -/
theorem nuclearNorm_mul_le_frobenius (A B : Matrix ι ι ℂ) :
    nuclearNorm (A*B) ≤ frobeniusNorm A*frobeniusNorm B := by
  apply nuclearNorm_le_of_pairing
  intro Q hQ
  calc
    _ = ‖((Aᴴ*Q)ᴴ*B).trace‖ := by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ ≤ frobeniusNorm (Aᴴ*Q)*frobeniusNorm B := trace_pairing_le_frobenius _ _
    _ ≤ frobeniusNorm A*frobeniusNorm B := by
      apply mul_le_mul_of_nonneg_right _ (frobeniusNorm_nonneg B)
      exact (frobeniusNorm_mul_le_op_right Aᴴ Q).trans (by
        simpa only [frobeniusNorm_conjTranspose,mul_one] using
          mul_le_mul_of_nonneg_left hQ (frobeniusNorm_nonneg A))

theorem nuclearNorm_mul_le_nuclear (A B : Matrix ι ι ℂ) :
    nuclearNorm (A*B) ≤ nuclearNorm A*nuclearNorm B := by
  exact (nuclearNorm_mul_le_op_left A B).trans
    (mul_le_mul_of_nonneg_right ((opNorm_le_frobeniusNorm A).trans (frobeniusNorm_le_nuclearNorm A))
      (nuclearNorm_nonneg B))
end NuclearInequalities
