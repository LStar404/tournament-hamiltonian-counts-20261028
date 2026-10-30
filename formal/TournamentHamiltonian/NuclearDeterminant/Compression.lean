module

public import TournamentHamiltonian.NuclearInequalities.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearDeterminant
open Matrix NuclearPolar NuclearInequalities WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rectangular intermediate is only used to prove square principal compression. -/
theorem row_submatrix_opNorm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (Z : Matrix m n ℂ) (R : Finset m) :
    ‖Z.submatrix (fun i : R => i.val) id‖ ≤ ‖Z‖ := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Z) ?_
  intro v
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg Z) (norm_nonneg v))
  have h := pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_mulVec Z v) 2
  rw [mul_pow] at h
  have hsubset : (∑ i : R, ‖(Z *ᵥ v) i.val‖^2) ≤ ∑ i, ‖(Z *ᵥ v) i‖^2 := by
    simp only [Finset.univ_eq_attach]
    rw [Finset.sum_attach R (fun i => ‖(Z *ᵥ v) i‖^2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun i _ _ => sq_nonneg _)
  have hsq : ‖((Matrix.toEuclideanLin (𝕜:=ℂ)).trans LinearMap.toContinuousLinearMap
      (Z.submatrix (fun i : R => i.val) id)) v‖^2 = ∑ i : R, ‖(Z *ᵥ v) i.val‖^2 := by
    change ‖toLp 2 ((Z.submatrix (fun i : R => i.val) id) *ᵥ v)‖^2 = _
    simp [PiLp.norm_sq_eq_of_L2,Matrix.mulVec,dotProduct]
  rw [hsq,mul_pow]
  exact hsubset.trans (by simpa [PiLp.norm_sq_eq_of_L2] using h)

/-- Principal compression of an actual complex Euclidean operator is a contraction. -/
theorem principal_opNorm_le (Q : Matrix ι ι ℂ) (S : Finset ι) :
    ‖Q.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)‖ ≤ ‖Q‖ := by
  have h := row_submatrix_opNorm_le (Q.submatrix (fun i : S => i.val) id)ᴴ S
  have he : (Q.submatrix (fun i : S => i.val) id)ᴴ.submatrix (fun j : S => j.val) id =
      (Q.submatrix (fun i : S => i.val) (fun j : S => j.val))ᴴ := by ext i j; rfl
  rw [he,Matrix.l2_opNorm_conjTranspose,Matrix.l2_opNorm_conjTranspose] at h
  exact h.trans (row_submatrix_opNorm_le Q S)

theorem det_spectralConj (M A : Matrix ι ι ℂ) : (spectralConj M A).det = A.det := by
  rw [spectralConj,Unitary.conjStarAlgAut_apply,Matrix.det_mul,Matrix.det_mul]
  calc
    _ = A.det * (star ((modulus_posSemidef M).isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      ((modulus_posSemidef M).isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)).det := by
        rw [Matrix.det_mul]; ring
    _ = A.det := by rw [Unitary.coe_star_mul_self,Matrix.det_one,mul_one]

/-- The actual determinant modulus is the product of the true nonnegative spectral values. -/
theorem norm_det_eq_prod_spectralValues (Q : Matrix ι ι ℂ) :
    ‖Q.det‖ = ∏ i, spectralValues Q i := by
  have he : ‖Q.det‖^2 = (∏ i, spectralValues Q i)^2 := by
    calc
      _ = ‖(Qᴴ*Q).det‖ := by simp [Matrix.det_mul,Matrix.det_conjTranspose,pow_two]
      _ = ‖(diagonal (fun i => ((spectralValues Q i)^2 : ℂ))).det‖ := by
        rw [gram_spectral,det_spectralConj]
      _ = (∏ i, spectralValues Q i)^2 := by
        rw [Matrix.det_diagonal,norm_prod,← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro i _
        simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg Q i)]
  nlinarith [norm_nonneg Q.det,Finset.prod_nonneg (s:=Finset.univ) (fun i _ => spectralValues_nonneg Q i)]

theorem norm_det_le_one_of_opNorm_le_one (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) : ‖Q.det‖≤1 := by
  rw [norm_det_eq_prod_spectralValues]
  apply Finset.prod_le_one₀ (fun i _ => spectralValues_nonneg Q i)
  intro i _
  have h := norm_le_pi_norm (fun j => (spectralValues Q j : ℂ)) i
  rw [← opNorm_eq_norm_spectralValues] at h
  have hh : spectralValues Q i ≤ ‖Q‖ := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg Q i)] using h
  exact hh.trans hQ

theorem principal_det_norm_le_one (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1) (S : Finset ι) :
    ‖(Q.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det‖ ≤ 1 :=
  norm_det_le_one_of_opNorm_le_one _ ((principal_opNorm_le Q S).trans hQ)
end NuclearDeterminant
