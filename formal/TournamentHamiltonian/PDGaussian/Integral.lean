module

public import TournamentHamiltonian.PDGaussian.Spectral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PDGaussian
open Matrix MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

def normalization (A : Matrix ι ι ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι / Real.sqrt A.det

theorem half_power (r : ℝ) (hr : 0 < r) :
    ((Real.pi : ℂ) / ((r : ℂ) / 2)) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * Real.pi) / Real.sqrt r : ℝ) : ℂ) := by
  have he : (Real.pi : ℂ) / ((r : ℂ) / 2) = ((2 * Real.pi / r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  have hp : 0 ≤ 2 * Real.pi / r := by positivity
  have hcast := Complex.ofReal_cpow hp (1 / 2 : ℝ)
  have he2 : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [he2] at hcast
  rw [← hcast, ← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity)]

theorem diagonal_integral (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (c : ι → ℂ) :
    (∫ x : ι → ℝ, Complex.exp (-∑ i, ((lam i : ℂ)/2) * (x i : ℂ)^2 +
      ∑ i, c i * (x i : ℂ))) =
      (((Real.sqrt (2 * Real.pi)) ^ Fintype.card ι / Real.sqrt (∏ i, lam i) : ℝ) : ℂ) *
      Complex.exp ((∑ i, c i^2 / (lam i : ℂ)) / 2) := by
  have hp (i : ι) : 0 < ((lam i : ℂ) / 2).re := by simpa using (div_pos (hlam i) (by norm_num : (0:ℝ)<2))
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add hp]
  simp_rw [half_power _ (hlam _)]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hn : (∏ i, ((Real.sqrt (2 * Real.pi) / Real.sqrt (lam i) : ℝ) : ℂ)) =
      (((Real.sqrt (2 * Real.pi)) ^ Fintype.card ι / Real.sqrt (∏ i, lam i) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, Finset.prod_div_distrib, Finset.prod_const,
      ← Real.sqrt_prod _ (fun i _ => (hlam i).le)]
    simp only [Finset.card_univ]
  rw [hn]
  congr 2
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernel_integrable {A : Matrix ι ι ℝ} (hA : A.PosDef) (z : ι → ℂ) :
    Integrable (kernel A z) := by
  let e := hA.1.eigenvectorBasis.repr.symm
  have hd := GaussianFourier.integrable_cexp_neg_sum_mul_add
    (b := fun i => (hA.1.eigenvalues i : ℂ) / 2)
    (fun i => by simpa using (div_pos (hA.eigenvalues_pos i) (by norm_num : (0:ℝ)<2)))
    (eigenCoordinates hA.1 z)
  have he : Integrable (fun x : EuclideanSpace ℝ ι => kernel A z (e x)) := by
    rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    simpa only [Function.comp_def, e, kernel_eigen] using hd
  have hf : Integrable (fun x : EuclideanSpace ℝ ι => kernel A z x) :=
    (e.measurePreserving.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mp he
  exact ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding).mpr hf

/-- Ordinary Lebesgue Gaussian integral. The complex form is bilinear, not sesquilinear. -/
theorem kernel_integral {A : Matrix ι ι ℝ} (hA : A.PosDef) (z : ι → ℂ) :
    (∫ x : ι → ℝ, kernel A z x) =
      (normalization A : ℂ) * Complex.exp (bilinear A⁻¹ z / 2) := by
  let e := hA.1.eigenvectorBasis.repr.symm
  calc
    (∫ x : ι → ℝ, kernel A z x) =
        ∫ x : EuclideanSpace ℝ ι, kernel A z x :=
      (PiLp.volume_preserving_toLp ι).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding
        (fun x : EuclideanSpace ℝ ι => kernel A z x)
    _ = ∫ x : EuclideanSpace ℝ ι, kernel A z (e x) :=
      (e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding _).symm
    _ = ∫ x : ι → ℝ, kernel A z (e (WithLp.toLp 2 x)) :=
      ((PiLp.volume_preserving_toLp ι).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding _).symm
    _ = _ := by
      simp_rw [e, kernel_eigen]
      rw [diagonal_integral _ hA.eigenvalues_pos, ← bilinear_eigen hA z]
      rw [normalization, hA.1.det_eq_prod_eigenvalues]
      rfl

/-- The Pi measure used throughout is the product of one-dimensional Lebesgue measures. -/
theorem pi_volume_eq : (volume : Measure (ι → ℝ)) = Measure.pi (fun _ => (volume : Measure ℝ)) := rfl

/-- Fully unfolded public endpoint, valid also when the finite index type is empty. -/
theorem integral_exp_quadratic_complex {A : Matrix ι ι ℝ} (hA : A.PosDef) (z : ι → ℂ) :
    (∫ x : ι → ℝ, Complex.exp (-(↑(x ⬝ᵥ A *ᵥ x) : ℂ)/2 + ∑ i, z i*(x i : ℂ))) =
      (((Real.sqrt (2 * Real.pi))^Fintype.card ι / Real.sqrt A.det : ℝ) : ℂ) *
      Complex.exp ((z ⬝ᵥ (A⁻¹.map Complex.ofReal) *ᵥ z)/2) :=
  kernel_integral hA z

theorem normalization_pos {A : Matrix ι ι ℝ} (hA : A.PosDef) : 0 < normalization A := by
  unfold normalization
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _)
    (Real.sqrt_pos.mpr hA.det_pos)
end PDGaussian
