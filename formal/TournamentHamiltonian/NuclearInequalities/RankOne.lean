module

public import TournamentHamiltonian.NuclearInequalities.Products

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearInequalities
open Matrix NuclearPolar WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual outer product a bᴴ, with the complex conjugation on b. -/
def outer (a b : EuclideanSpace ℂ ι) : Matrix ι ι ℂ := vecMulVec (ofLp a) (star (ofLp b))

omit [DecidableEq ι] in
theorem frobeniusNorm_outer (a b : EuclideanSpace ℂ ι) :
    frobeniusNorm (outer a b) = ‖a‖*‖b‖ := by
  have he : frobeniusNorm (outer a b)^2 = (‖a‖*‖b‖)^2 := by
    rw [frobeniusNorm_sq,mul_pow,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp only [outer,Matrix.vecMulVec_apply,Pi.star_apply,norm_mul,norm_star,mul_pow,
      Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_comm
  nlinarith [frobeniusNorm_nonneg (outer a b),mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem trace_pairing_outer (Q : Matrix ι ι ℂ) (a b : EuclideanSpace ℂ ι) :
    (Qᴴ*outer a b).trace = inner ℂ b (toEuclideanCLM (𝕜:=ℂ) (n:=ι) Qᴴ a) := by
  rw [outer,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM]

theorem nuclearNorm_outer_le (a b : EuclideanSpace ℂ ι) :
    nuclearNorm (outer a b) ≤ ‖a‖*‖b‖ := by
  apply nuclearNorm_le_of_pairing
  intro Q hQ
  rw [trace_pairing_outer]
  calc
    _ ≤ ‖b‖*‖toEuclideanCLM (𝕜:=ℂ) (n:=ι) Qᴴ a‖ := norm_inner_le_norm _ _
    _ ≤ ‖b‖*(‖Qᴴ‖*‖a‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
      simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
        (toEuclideanCLM (𝕜:=ℂ) (n:=ι) Qᴴ).le_opNorm a
    _ ≤ ‖b‖*(1*‖a‖) := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ (norm_nonneg a)) (norm_nonneg b)
    _ = ‖a‖*‖b‖ := by ring

/-- No nonzero assumption: zero vectors and the empty index type are included. -/
theorem nuclearNorm_outer (a b : EuclideanSpace ℂ ι) :
    nuclearNorm (outer a b) = ‖a‖*‖b‖ := by
  apply le_antisymm (nuclearNorm_outer_le a b)
  rw [← frobeniusNorm_outer]
  exact frobeniusNorm_le_nuclearNorm _
end NuclearInequalities
