module

public import TournamentHamiltonian.NuclearDeterminant.Compression
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearDeterminant
open Matrix NuclearPolar NuclearInequalities Polynomial
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex principal-minor generating identity, including the empty principal minor. -/
theorem det_one_add_eq_sum_principal (M : Matrix ι ι ℂ) :
    (1+M).det = ∑ S : Finset ι, (M.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det := by
  have hpu : (Finset.univ : Finset ι).powerset = Finset.univ := by ext S; simp
  have hp : ((1:Matrix ι ι ℂ[X])+(X:ℂ[X]) • M.map C).det =
      ∑ S : Finset ι, C (M.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det * X^S.card := by
    ext k
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    simp only [Finset.powersetCard_eq_filter,hpu,Finset.sum_filter,Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    apply Finset.sum_congr rfl
    intro S _
    simp only [eq_comm]
  have hm := (Polynomial.evalRingHom (1:ℂ)).map_det ((1:Matrix ι ι ℂ[X])+(X:ℂ[X]) • M.map C)
  have heq : (((1:Matrix ι ι ℂ[X])+(X:ℂ[X]) • M.map C).map (Polynomial.evalRingHom (1:ℂ))) = 1+M := by
    ext i j
    change Polynomial.eval 1 ((if i=j then (1:ℂ[X]) else 0)+(X:ℂ[X])*C (M i j)) =
      (if i=j then (1:ℂ) else 0)+M i j
    rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    split_ifs <;> simp only [Polynomial.eval_one,Polynomial.eval_zero,one_mul]
  change Polynomial.eval 1 ((1:Matrix ι ι ℂ[X])+(X:ℂ[X]) • M.map C).det =
    (((1:Matrix ι ι ℂ[X])+(X:ℂ[X]) • M.map C).map (Polynomial.evalRingHom (1:ℂ))).det at hm
  rw [heq,hp] at hm
  rw [← hm,Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro S _
  simp

theorem principal_mul_diagonal (Q : Matrix ι ι ℂ) (s : ι → ℝ) (S : Finset ι) :
    (Q*diagonal (fun i => (s i:ℂ))).submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) =
      Q.submatrix (Subtype.val : S → ι) (Subtype.val : S → ι) * diagonal (fun i : S => (s i:ℂ)) := by
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.mul_diagonal]

theorem principal_weighted_det_bound (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1)
    (s : ι → ℝ) (hs : ∀ i, 0≤s i) (S : Finset ι) :
    ‖((Q*diagonal (fun i => (s i:ℂ))).submatrix (Subtype.val : S → ι) (Subtype.val : S → ι)).det‖ ≤
      ∏ i ∈ S, s i := by
  rw [principal_mul_diagonal,Matrix.det_mul,norm_mul,Matrix.det_diagonal,norm_prod]
  have hp : (∏ i : S, ‖(s i : ℂ)‖) = ∏ i ∈ S, s i := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs _),Finset.univ_eq_attach]
    exact Finset.prod_attach S s
  rw [hp]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (principal_det_norm_le_one Q hQ S)
    (Finset.prod_nonneg fun i _ => hs i)

omit [DecidableEq ι] in
theorem sum_subset_prod (s : ι → ℝ) :
    (∑ S : Finset ι, ∏ i ∈ S, s i) = ∏ i, (1+s i) := by
  have hpu : (Finset.univ : Finset ι).powerset = Finset.univ := by ext S; simp
  simpa only [hpu] using (Finset.prod_one_add (f:=s) Finset.univ).symm

/-- A contraction times an actual nonnegative diagonal has the required perturbation bound. -/
theorem det_one_add_contraction_diagonal (Q : Matrix ι ι ℂ) (hQ : ‖Q‖≤1)
    (s : ι → ℝ) (hs : ∀ i, 0≤s i) :
    ‖(1+Q*diagonal (fun i => (s i:ℂ))).det‖ ≤ ∏ i, (1+s i) := by
  rw [det_one_add_eq_sum_principal]
  calc
    _ ≤ ∑ S : Finset ι, ‖((Q*diagonal (fun i => (s i:ℂ))).submatrix
        (Subtype.val : S → ι) (Subtype.val : S → ι)).det‖ := norm_sum_le _ _
    _ ≤ ∑ S : Finset ι, ∏ i ∈ S, s i := Finset.sum_le_sum (fun S _ => principal_weighted_det_bound Q hQ s hs S)
    _ = ∏ i, (1+s i) := sum_subset_prod s
end NuclearDeterminant
