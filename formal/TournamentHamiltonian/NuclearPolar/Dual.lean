module

public import TournamentHamiltonian.NuclearPolar.Polar

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearPolar
open Matrix WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem entry_norm_le_opNorm (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  have h := (toEuclideanCLM (𝕜:=ℂ) (n:=ι) A).le_opNorm (PiLp.single 2 j (1:ℂ))
  have h' : ‖toEuclideanCLM (𝕜:=ℂ) (n:=ι) A (PiLp.single 2 j (1:ℂ))‖ ≤ ‖A‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM,PiLp.norm_single,norm_one,mul_one] using h
  have he := PiLp.norm_apply_le (toEuclideanCLM (𝕜:=ℂ) (n:=ι) A (PiLp.single 2 j (1:ℂ))) i
  change ‖(ofLp (toEuclideanCLM (𝕜:=ℂ) (n:=ι) A (PiLp.single 2 j (1:ℂ)))) i‖ ≤ _ at he
  rw [Matrix.ofLp_toEuclideanCLM,PiLp.ofLp_single,Matrix.mulVec_single_one] at he
  exact he.trans h'

theorem trace_modulus_bound (M A : Matrix ι ι ℂ) :
    ‖(A*modulus M).trace‖ ≤ ‖A‖*nuclearNorm M := by
  let C := (spectralConj M).symm A
  have ht : (A*modulus M).trace = (C*diagonal (fun i => (spectralValues M i : ℂ))).trace := by
    rw [← trace_spectralConj M (C*diagonal (fun i => (spectralValues M i : ℂ))),map_mul]
    simp only [C,StarAlgEquiv.apply_symm_apply,← modulus_spectral]
  rw [ht]
  calc
    _ = ‖∑ i, C i i*(spectralValues M i : ℂ)‖ := by simp [Matrix.trace,Matrix.mul_diagonal]
    _ ≤ ∑ i, ‖C i i*(spectralValues M i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖C‖*spectralValues M i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg M i)]
      exact mul_le_mul_of_nonneg_right (entry_norm_le_opNorm C i i) (spectralValues_nonneg M i)
    _ = ‖A‖*nuclearNorm M := by
      rw [← Finset.mul_sum,nuclearNorm_eq_sum_spectralValues,show ‖C‖=‖A‖ from norm_spectralConj_symm M A]

/-- Actual trace pairing bound for every complex square Q, not only unitary Q. -/
theorem trace_pairing_le (M Q : Matrix ι ι ℂ) :
    ‖(Qᴴ*M).trace‖ ≤ ‖Q‖*nuclearNorm M := by
  calc
    _ = ‖((Qᴴ*polarFactor M)*modulus M).trace‖ := by rw [mul_assoc,← polar_factorization]
    _ ≤ ‖Qᴴ*polarFactor M‖*nuclearNorm M := trace_modulus_bound M _
    _ ≤ ‖Q‖*nuclearNorm M := by
      apply mul_le_mul_of_nonneg_right _ (nuclearNorm_nonneg M)
      calc
        _ ≤ ‖Qᴴ‖*‖polarFactor M‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖Q‖*1 := by
          rw [Matrix.l2_opNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_left (polarFactor_norm_le_one M) (norm_nonneg Q)
        _ = ‖Q‖ := mul_one _

/-- The maximum is genuinely attained, even with zero singular values. -/
theorem exists_dual_attainer (M : Matrix ι ι ℂ) :
    ∃ Q : Matrix ι ι ℂ, ‖Q‖ ≤ 1 ∧ (Qᴴ*M).trace = (nuclearNorm M : ℂ) := by
  refine ⟨polarFactor M,polarFactor_norm_le_one M,?_⟩
  rw [polarFactor_star_mul,trace_modulus]

/-- Literal dual maximum over the actual operator unit ball, not a proxy norm definition. -/
theorem nuclearNorm_dual_max (M : Matrix ι ι ℂ) :
    IsGreatest ((fun Q : Matrix ι ι ℂ => ‖(Qᴴ*M).trace‖) '' {Q | ‖Q‖ ≤ 1}) (nuclearNorm M) := by
  constructor
  · exact ⟨polarFactor M,polarFactor_norm_le_one M,polarFactor_attains_trace M⟩
  · rintro z ⟨Q,hQ,rfl⟩
    exact (trace_pairing_le M Q).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ (nuclearNorm_nonneg M))
end NuclearPolar
