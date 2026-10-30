module

public import TournamentHamiltonian.ForestGaussianIntegral.CompleteRoot
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PDGaussian
open Matrix MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := A.map Complex.ofReal

def eigenCoordinates {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (z : ι → ℂ) : ι → ℂ :=
  z ᵥ* complexify (hA.eigenvectorUnitary : Matrix ι ι ℝ)

def bilinear (A : Matrix ι ι ℝ) (z : ι → ℂ) : ℂ := z ⬝ᵥ complexify A *ᵥ z

def kernel (A : Matrix ι ι ℝ) (z : ι → ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp (-(↑(x ⬝ᵥ A *ᵥ x) : ℂ) / 2 + ∑ i, z i * (x i : ℂ))

theorem eigen_inverse {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹ = (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) *
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) *
      (hA.1.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ := by
  let U : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  have hu : U * Uᵀ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have hut : Uᵀ * U = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hs : A = U * diagonal hA.1.eigenvalues * Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hA.1.spectral_theorem
  apply Matrix.inv_eq_right_inv
  change A * (U * diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * Uᵀ) = 1
  conv_lhs => arg 1; rw [hs]
  calc
    U * diagonal hA.1.eigenvalues * Uᵀ *
        (U * diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * Uᵀ) =
        U * (diagonal hA.1.eigenvalues * diagonal (fun i => (hA.1.eigenvalues i)⁻¹)) * Uᵀ := by
          simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hut, one_mul]
    _ = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have he : (fun i => hA.1.eigenvalues i * (hA.1.eigenvalues i)⁻¹) = fun _ => (1 : ℝ) := by
        funext i
        exact mul_inv_cancel₀ (ne_of_gt (hA.eigenvalues_pos i))
      rw [he, Matrix.diagonal_one, mul_one, hu]

theorem complexify_mul (A B : Matrix ι ι ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem bilinear_eigen {A : Matrix ι ι ℝ} (hA : A.PosDef) (z : ι → ℂ) :
    bilinear A⁻¹ z = ∑ i, (eigenCoordinates hA.1 z i)^2 / (hA.1.eigenvalues i : ℂ) := by
  rw [bilinear, eigen_inverse hA, complexify_mul, complexify_mul]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  have ht : complexify (hA.1.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ =
      (complexify (hA.1.eigenvectorUnitary : Matrix ι ι ℝ))ᵀ := rfl
  rw [ht, Matrix.mulVec_transpose]
  rw [Matrix.dotProduct_mulVec]
  change (eigenCoordinates hA.1 z ᵥ* complexify (diagonal (fun i => (hA.1.eigenvalues i)⁻¹))) ⬝ᵥ
      eigenCoordinates hA.1 z = _
  have hd : complexify (diagonal (fun i => (hA.1.eigenvalues i)⁻¹)) =
      diagonal (fun i => (hA.1.eigenvalues i : ℂ)⁻¹) := by
    ext i j
    by_cases h : i = j <;> simp [complexify, h]
  rw [hd]
  simp only [dotProduct, Matrix.vecMul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eigenbasis_apply {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) (j : ι) :
    hA.eigenvectorBasis.repr.symm (WithLp.toLp 2 x) j =
      ∑ i, x i * hA.eigenvectorBasis i j := by
  rw [← hA.eigenvectorBasis.sum_repr_symm]
  simp

theorem kernel_eigen {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (z : ι → ℂ) (x : ι → ℝ) :
    kernel A z (hA.eigenvectorBasis.repr.symm (WithLp.toLp 2 x)) =
    Complex.exp (-∑ i, ((hA.eigenvalues i : ℂ) / 2) * (x i : ℂ)^2 +
      ∑ i, eigenCoordinates hA z i * (x i : ℂ)) := by
  have hq : (hA.eigenvectorBasis.repr.symm (WithLp.toLp 2 x) : ι → ℝ) ⬝ᵥ
      A *ᵥ (hA.eigenvectorBasis.repr.symm (WithLp.toLp 2 x) : ι → ℝ) =
      ∑ i, hA.eigenvalues i * (x i)^2 := by
    have h := TournamentHamiltonian.hermitian_quadratic_eigenbasis hA x
    have he := hA.eigenvectorBasis.sum_repr_symm (WithLp.toLp 2 x)
    change (∑ i, x i • hA.eigenvectorBasis i) = _ at he
    rw [he] at h
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      Matrix.toLpLin_apply, dotProduct_comm] using h
  have hl : (∑ j, z j * (hA.eigenvectorBasis.repr.symm (WithLp.toLp 2 x) j : ℂ)) =
      ∑ i, eigenCoordinates hA z i * (x i : ℂ) := by
    simp only [eigenbasis_apply, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.mul_sum, eigenCoordinates, Matrix.vecMul, dotProduct, complexify,
      Matrix.map_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [kernel, hq, hl]
  congr 2
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, neg_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring
end PDGaussian
