module

public import TournamentHamiltonian.GaussianFactorialRecovery

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

theorem gramPSD (B : Matrix ι ι ℝ) : (B.transpose*B).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self B

def gramEigenvalues (B : Matrix ι ι ℝ) : ι → ℝ := (gramPSD B).isHermitian.eigenvalues

theorem gramEigenvalues_nonneg (B : Matrix ι ι ℝ) (i : ι) : 0≤gramEigenvalues B i :=
  (gramPSD B).eigenvalues_nonneg i

theorem gramEigenvalues_le (B : Matrix ι ι ℝ) (q : ℝ) (_hq : 0≤q) (hB : ‖B‖≤q) (i : ι) :
    gramEigenvalues B i≤q^2 := by
  let : Nonempty ι := ⟨i⟩
  have h := spectrum.norm_le_norm_of_mem ((gramPSD B).isHermitian.eigenvalues_mem_spectrum_real i)
  have he : gramEigenvalues B i≤‖B.transpose*B‖ := by
    change ‖gramEigenvalues B i‖≤‖B.transpose*B‖ at h
    simpa only [Real.norm_eq_abs,abs_of_nonneg (gramEigenvalues_nonneg B i)] using h
  have ht : ‖B.transpose‖=‖B‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose B
  calc
    _ ≤ ‖B.transpose*B‖ := he
    _ ≤ ‖B.transpose‖*‖B‖ := norm_mul_le _ _
    _ = ‖B‖^2 := by rw [ht]; ring
    _ ≤ q^2 := pow_le_pow_left₀ (norm_nonneg B) hB 2

theorem gramEigenvalues_sum (B : Matrix ι ι ℝ) :
    (∑ i,gramEigenvalues B i)=realFrobeniusNorm B^2 := by
  have ht : (B.transpose*B).trace=∑ i,gramEigenvalues B i := by
    simpa [gramEigenvalues] using (gramPSD B).isHermitian.trace_eq_sum_eigenvalues
  rw [←ht,realFrobeniusNorm_sq]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,←pow_two]
  exact Finset.sum_comm

/-- Fixed Gram eigenvalues diagonalize the entire scalar path; no differentiated
eigenvector choice or full singular-value decomposition is introduced. -/
theorem det_gram_scale (B : Matrix ι ι ℝ) (t : ℝ) :
    ((1 : Matrix ι ι ℝ)-(t • B).transpose*(t • B)).det =
      ∏ i, (1-t^2*gramEigenvalues B i) := by
  let h := (gramPSD B).isHermitian
  have hscale : (t • B).transpose*(t • B)=t^2 • (B.transpose*B) := by
    simp [Matrix.transpose_smul,smul_smul,pow_two]
  rw [hscale]
  have he : (1 : Matrix ι ι ℝ)-t^2 • (B.transpose*B) =
      Unitary.conjStarAlgAut ℝ _ h.eigenvectorUnitary
        (1-t^2 • Matrix.diagonal h.eigenvalues) := by
    rw [map_sub,map_one,map_smul]
    exact congrArg (fun A => (1 : Matrix ι ι ℝ)-t^2 • A) h.spectral_theorem
  rw [he,Unitary.conjStarAlgAut_apply,Matrix.det_mul_right_comm,
    ←Unitary.coe_star,Unitary.coe_mul_star_self,one_mul]
  have hd : (1 : Matrix ι ι ℝ)-t^2 • Matrix.diagonal h.eigenvalues =
      Matrix.diagonal (fun i => 1-t^2*gramEigenvalues B i) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,hij,gramEigenvalues]
  rw [hd,Matrix.det_diagonal]

end
end PaperGaussianRecovery
