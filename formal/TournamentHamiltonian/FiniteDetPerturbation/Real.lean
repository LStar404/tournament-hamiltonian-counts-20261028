module

public import TournamentHamiltonian.FiniteDetPerturbation.Perturbation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FiniteDetPerturbation
open Matrix NuclearPolar NuclearInequalities NuclearDeterminant AccretiveInverse
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual entrywise complexification, as a unital matrix ring homomorphism. -/
def complexify : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

theorem complexify_apply (A : Matrix ι ι ℝ) (i j : ι) : complexify A i j=(A i j:ℂ) := rfl

theorem complexify_transpose (A : Matrix ι ι ℝ) : complexify Aᵀ=(complexify A)ᴴ := by
  ext i j
  simp [complexify,Matrix.conjTranspose_apply]

theorem complexify_det (A : Matrix ι ι ℝ) : (complexify A).det=(A.det:ℂ) :=
  (Complex.ofRealHom.map_det A).symm

theorem complexify_posSemidef (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have he : complexify A=(complexify R)ᴴ*complexify R := by
    rw [hR,map_mul]
    congr 1
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      complexify_transpose R
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The real symmetric-part hypothesis really implies the complex Hermitian-part hypothesis. -/
theorem complexify_accretive (W : Matrix ι ι ℝ)
    (hW : (1:Matrix ι ι ℝ) ≤ (1/2:ℝ) • (W+Wᵀ)) :
    (1:Matrix ι ι ℂ) ≤ (1/2:ℂ) • (complexify W+(complexify W)ᴴ) := by
  have h := complexify_posSemidef (((1/2:ℝ) • (W+Wᵀ))-1) (Matrix.le_iff.mp hW)
  apply Matrix.le_iff.mpr
  convert h using 1
  ext i j
  simp [complexify,Matrix.sub_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
    Matrix.conjTranspose_apply]
  split_ifs <;> norm_num

theorem real_abs_det_add_le_exp_nuclear (W Δ : Matrix ι ι ℝ)
    (hW : (1:Matrix ι ι ℝ) ≤ (1/2:ℝ) • (W+Wᵀ)) :
    |(W+Δ).det| ≤ |W.det| * Real.exp (nuclearNorm (complexify Δ)) := by
  have h := norm_det_add_le_exp_nuclear (complexify W) (complexify Δ) (complexify_accretive W hW)
  simpa only [← map_add,complexify_det,Complex.norm_real,Real.norm_eq_abs] using h

/-- Positivity of det W is explicit; no positivity or invertibility of W+Δ is needed here. -/
theorem real_det_add_le_exp_nuclear (W Δ : Matrix ι ι ℝ)
    (hW : (1:Matrix ι ι ℝ) ≤ (1/2:ℝ) • (W+Wᵀ)) (hdet : 0<W.det) :
    (W+Δ).det ≤ W.det*Real.exp (nuclearNorm (complexify Δ)) := by
  exact (le_abs_self _).trans (by
    simpa only [abs_of_pos hdet] using real_abs_det_add_le_exp_nuclear W Δ hW)

/-- Guarded real logdet consequence. Both determinant positivity hypotheses are retained. -/
theorem real_logdet_add_sub_le_nuclear (W Δ : Matrix ι ι ℝ)
    (hW : (1:Matrix ι ι ℝ) ≤ (1/2:ℝ) • (W+Wᵀ))
    (hdet : 0<W.det) (hpert : 0<(W+Δ).det) :
    Real.log (W+Δ).det-Real.log W.det ≤ nuclearNorm (complexify Δ) := by
  have h := Real.log_le_log hpert (real_det_add_le_exp_nuclear W Δ hW hdet)
  rw [Real.log_mul hdet.ne' (Real.exp_ne_zero _),Real.log_exp] at h
  linarith

theorem real_logdet_add_sub_le_budget (W Δ : Matrix ι ι ℝ)
    (hW : (1:Matrix ι ι ℝ) ≤ (1/2:ℝ) • (W+Wᵀ))
    (hdet : 0<W.det) (hpert : 0<(W+Δ).det) {B : ℝ} (hΔ : nuclearNorm (complexify Δ)≤B) :
    Real.log (W+Δ).det-Real.log W.det ≤ B :=
  (real_logdet_add_sub_le_nuclear W Δ hW hdet hpert).trans hΔ
end FiniteDetPerturbation
