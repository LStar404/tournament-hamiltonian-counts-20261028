module

public import TournamentHamiltonian.NuclearInequalities.Algebra
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearInequalities
open Matrix NuclearPolar WithLp
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Frobenius norm explicitly as the Euclidean norm of all complex entries. -/
def frobeniusNorm (M : Matrix ι ι ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖M i j‖^2)

omit [DecidableEq ι] in
theorem frobeniusNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ frobeniusNorm M := Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem frobeniusNorm_sq (M : Matrix ι ι ℂ) :
    frobeniusNorm M^2 = ∑ i, ∑ j, ‖M i j‖^2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

omit [DecidableEq ι] in
theorem frobeniusNorm_sq_eq_trace (M : Matrix ι ι ℂ) :
    frobeniusNorm M^2 = (Mᴴ*M).trace.re := by
  rw [frobeniusNorm_sq,Matrix.trace_mul_comm]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum,Matrix.mul_apply,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change ‖M i j‖^2 = (M i j * (starRingEnd ℂ) (M i j)).re
  rw [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]

omit [DecidableEq ι] in
theorem frobeniusNorm_conjTranspose (M : Matrix ι ι ℂ) :
    frobeniusNorm Mᴴ = frobeniusNorm M := by
  simp only [frobeniusNorm,Matrix.conjTranspose_apply,norm_star]
  rw [Finset.sum_comm]

/-- These are genuine singular values: their squares diagonalize the actual Gram matrix. -/
theorem gram_spectral (M : Matrix ι ι ℂ) :
    Mᴴ*M = spectralConj M (diagonal (fun i => ((spectralValues M i)^2 : ℂ))) := by
  rw [← modulus_sq,modulus_spectral,← map_mul,diagonal_mul_diagonal]
  congr 2
  ext i
  simp [pow_two]

theorem frobeniusNorm_sq_eq_sum_spectralValues (M : Matrix ι ι ℂ) :
    frobeniusNorm M^2 = ∑ i, spectralValues M i^2 := by
  rw [frobeniusNorm_sq_eq_trace,← modulus_sq,modulus_spectral,← map_mul,trace_spectralConj]
  simp only [diagonal_mul_diagonal,trace_diagonal,Complex.re_sum,← Complex.ofReal_mul,
    Complex.ofReal_re,pow_two]

theorem frobeniusNorm_eq_sqrt_spectralValues (M : Matrix ι ι ℂ) :
    frobeniusNorm M = Real.sqrt (∑ i, spectralValues M i^2) := by
  rw [← frobeniusNorm_sq_eq_sum_spectralValues,Real.sqrt_sq (frobeniusNorm_nonneg M)]

theorem opNorm_eq_norm_spectralValues (M : Matrix ι ι ℂ) :
    ‖M‖ = ‖fun i => (spectralValues M i : ℂ)‖ := by
  rw [← modulus_norm,modulus_spectral,norm_spectralConj,Matrix.l2_opNorm_diagonal]

theorem opNorm_le_frobeniusNorm (M : Matrix ι ι ℂ) : ‖M‖ ≤ frobeniusNorm M := by
  rw [opNorm_eq_norm_spectralValues]
  apply (pi_norm_le_iff_of_nonneg (frobeniusNorm_nonneg M)).mpr
  intro i
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg M i)]
  apply le_of_sq_le_sq _ (frobeniusNorm_nonneg M)
  rw [frobeniusNorm_sq_eq_sum_spectralValues]
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem frobeniusNorm_le_nuclearNorm (M : Matrix ι ι ℂ) : frobeniusNorm M ≤ nuclearNorm M := by
  apply le_of_sq_le_sq _ (nuclearNorm_nonneg M)
  rw [frobeniusNorm_sq_eq_sum_spectralValues,nuclearNorm_eq_sum_spectralValues]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => spectralValues_nonneg M i)

theorem nuclearNorm_le_sqrt_card_mul_frobeniusNorm (M : Matrix ι ι ℂ) :
    nuclearNorm M ≤ Real.sqrt (Fintype.card ι) * frobeniusNorm M := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (frobeniusNorm_nonneg M))
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),frobeniusNorm_sq_eq_sum_spectralValues,
    nuclearNorm_eq_sum_spectralValues]
  simpa using sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=spectralValues M)

omit [DecidableEq ι] in
theorem trace_pairing_le_frobenius (A B : Matrix ι ι ℂ) :
    ‖(Aᴴ*B).trace‖ ≤ frobeniusNorm A*frobeniusNorm B := by
  calc
    _ = ‖∑ p : ι × ι, star (A p.1 p.2)*B p.1 p.2‖ := by
      simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    _ ≤ ∑ p : ι × ι, ‖star (A p.1 p.2)*B p.1 p.2‖ := norm_sum_le _ _
    _ = ∑ p : ι × ι, ‖A p.1 p.2‖*‖B p.1 p.2‖ := by simp only [norm_mul,norm_star]
    _ ≤ frobeniusNorm A*frobeniusNorm B := by
      simpa [frobeniusNorm,Fintype.sum_prod_type] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun p : ι × ι => ‖A p.1 p.2‖) (fun p : ι × ι => ‖B p.1 p.2‖)

/-- The literal maximum of singular values; nonempty is needed only for the maximum. -/
theorem opNorm_isGreatest_spectralValues [Nonempty ι] (M : Matrix ι ι ℂ) :
    IsGreatest (Set.range (spectralValues M)) ‖M‖ := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (spectralValues M) Finset.univ_nonempty
  have hs : ‖M‖ = spectralValues M i := by
    rw [opNorm_eq_norm_spectralValues]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (spectralValues_nonneg M i)).mpr
      intro j
      simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg M j)] using hi j (Finset.mem_univ j)
    · simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (spectralValues_nonneg M i)] using
        norm_le_pi_norm (fun j => (spectralValues M j : ℂ)) i
  constructor
  · exact ⟨i,hs.symm⟩
  · rintro _ ⟨j,rfl⟩
    rw [hs]
    exact hi j (Finset.mem_univ j)

theorem nuclearNorm_eq_zero_iff (M : Matrix ι ι ℂ) : nuclearNorm M = 0 ↔ M = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    have hb := (opNorm_le_frobeniusNorm M).trans (frobeniusNorm_le_nuclearNorm M)
    rw [h] at hb
    exact le_antisymm hb (norm_nonneg M)
  · rintro rfl
    simp [nuclearNorm,modulus,CFC.abs_zero]

section FrobeniusConvention
open scoped Matrix.Norms.Frobenius
theorem frobeniusNorm_eq_matrixFrobenius (M : Matrix ι ι ℂ) : frobeniusNorm M = ‖M‖ := by
  simp only [frobeniusNorm,Matrix.frobenius_norm_def,Real.sqrt_eq_rpow,Real.rpow_two]
end FrobeniusConvention
end NuclearInequalities
