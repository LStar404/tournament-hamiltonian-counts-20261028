module

public import TournamentHamiltonian.GaussianMGF
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TournamentHamiltonian.ForestGaussian.SpectralEstimate

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace ForestGaussian
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

/-- The actual scaled complement, with no restriction to a hyperplane. -/
def complement (L : Matrix ι ι ℝ) (m : ℝ) : Matrix ι ι ℝ := 1 - m⁻¹ • L

/-- The determinant–phase factor formed from the actual matrix inverse. -/
def factor (L : Matrix ι ι ℝ) (b : ι → ℝ) (m : ℝ) : ℝ :=
  (Real.sqrt (complement L m).det)⁻¹ *
    Real.exp (-(b ⬝ᵥ (complement L m)⁻¹ *ᵥ b) / (2 * m))

theorem eigenvector_sum_sq {L : Matrix ι ι ℝ} (hL : L.IsHermitian) (i : ι) :
    ∑ j, (hL.eigenvectorBasis i j) ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (hL.eigenvectorBasis i)
  rw [hL.eigenvectorBasis.orthonormal.1 i] at h
  simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm

theorem eigenvalues_le_four {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2) (i : ι) :
    hL.eigenvalues i ≤ 4 := by
  have h := hbound (hL.eigenvectorBasis i)
  rw [hL.mulVec_eigenvectorBasis, dotProduct_smul] at h
  simp only [smul_eq_mul, dotProduct] at h
  simp_rw [← pow_two] at h
  rw [eigenvector_sum_sq hL i] at h
  simpa using h

theorem eigenvalues_sum_sq_le {L : Matrix ι ι ℝ} (hL : L.PosSemidef)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2) :
    (∑ i, hL.isHermitian.eigenvalues i ^ 2) ≤ 4 * L.trace := by
  rw [hL.isHermitian.trace_eq_sum_eigenvalues, Finset.mul_sum]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.sum_le_sum
  intro i _
  have h0 := hL.eigenvalues_nonneg i
  have h4 := eigenvalues_le_four hL.isHermitian hbound i
  nlinarith

theorem complement_posDef {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2)
    {m : ℝ} (hm : 4 < m) : (complement L m).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_one.sub (hL.smul (by rw [IsSelfAdjoint]; simp))
  · intro x hx
    have hs : 0 < ∑ i, x i ^ 2 := by
      apply Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg _) |>.mpr
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hb := hbound x
    have hm0 : 0 < m := by linarith
    have hi : 0 < m⁻¹ := inv_pos.mpr hm0
    have hmul : m⁻¹ * (x ⬝ᵥ L *ᵥ x) ≤ m⁻¹ * (4 * ∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_left hb hi.le
    have hlt : m⁻¹ * 4 < 1 := by
      rw [inv_mul_eq_div, div_lt_one hm0]
      exact hm
    simp only [complement, star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have he : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, pow_two]
    rw [he]
    nlinarith

theorem factor_pos {L : Matrix ι ι ℝ} (b : ι → ℝ) {m : ℝ}
    (hK : (complement L m).PosDef) : 0 < factor L b m := by
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hK.det_pos)) (Real.exp_pos _)

theorem complement_det {L : Matrix ι ι ℝ} (hL : L.IsHermitian) (m : ℝ) :
    (complement L m).det = ∏ i, (1 - hL.eigenvalues i / m) := by
  have hdiag : Matrix.diagonal (fun i => 1 - hL.eigenvalues i / m) =
      (1 : Matrix ι ι ℝ) - m⁻¹ • Matrix.diagonal hL.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [div_eq_mul_inv, mul_comm]
    · simp [hij]
  have he : complement L m =
      Unitary.conjStarAlgAut ℝ _ hL.eigenvectorUnitary
        (Matrix.diagonal (fun i => 1 - hL.eigenvalues i / m)) := by
    rw [hdiag, map_sub, map_one, map_smul]
    have hs := hL.spectral_theorem
    simp only [RCLike.ofReal_real_eq_id, Function.id_comp] at hs
    rw [← hs]
    rfl
  rw [he, Unitary.conjStarAlgAut_apply, Matrix.det_mul_right_comm,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul, Matrix.det_diagonal]

theorem complement_eigenvector {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (m : ℝ) (i : ι) :
    complement L m *ᵥ (hL.eigenvectorBasis i : ι → ℝ) =
      (1 - hL.eigenvalues i / m) • (hL.eigenvectorBasis i : ι → ℝ) := by
  rw [complement, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    hL.mulVec_eigenvectorBasis, smul_smul, sub_smul, one_smul]
  simp [div_eq_mul_inv, mul_comm]

theorem complement_inv_eigenvector {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    {m : ℝ} (hK : (complement L m).PosDef)
    (hEig : ∀ i, 0 < 1 - hL.eigenvalues i / m) (i : ι) :
    (complement L m)⁻¹ *ᵥ (hL.eigenvectorBasis i : ι → ℝ) =
      (1 - hL.eigenvalues i / m)⁻¹ • (hL.eigenvectorBasis i : ι → ℝ) := by
  have hi := congrArg (fun x : ι → ℝ => (complement L m)⁻¹ *ᵥ x)
    (complement_eigenvector hL m i)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne'),
    Matrix.one_mulVec, Matrix.mulVec_smul] at hi
  have hi' := congrArg (fun x : ι → ℝ => (1 - hL.eigenvalues i / m)⁻¹ • x) hi
  simpa only [smul_smul, inv_mul_cancel₀ (hEig i).ne', one_smul] using hi'.symm

/-- Squared coordinates of the actual endpoint vector in the Laplacian eigenbasis. -/
def phaseCoordinates {L : Matrix ι ι ℝ} (hL : L.IsHermitian) (b : ι → ℝ) : ι → ℝ :=
  fun i => (hL.eigenvectorBasis.repr (WithLp.toLp 2 b) i) ^ 2

theorem phaseCoordinates_nonneg {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (b : ι → ℝ) (i : ι) : 0 ≤ phaseCoordinates hL b i := sq_nonneg _

theorem phaseCoordinates_sum {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (b : ι → ℝ) : ∑ i, phaseCoordinates hL b i = ∑ i, b i ^ 2 := by
  have h := hL.eigenvectorBasis.sum_sq_inner_right (WithLp.toLp 2 b)
  simpa only [phaseCoordinates, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_toLp] using h

theorem complement_inv_quadratic {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (b : ι → ℝ) {m : ℝ} (hK : (complement L m).PosDef)
    (hEig : ∀ i, 0 < 1 - hL.eigenvalues i / m) :
    b ⬝ᵥ (complement L m)⁻¹ *ᵥ b =
      ∑ i, phaseCoordinates hL b i / (1 - hL.eigenvalues i / m) := by
  have he (i : ι) : Matrix.toEuclideanLin (complement L m)⁻¹
      (hL.eigenvectorBasis i) =
      (1 - hL.eigenvalues i / m)⁻¹ • hL.eigenvectorBasis i := by
    ext a
    exact congrFun (complement_inv_eigenvector hL hK hEig i) a
  have hquad (x : ι → ℝ) :
      inner ℝ (∑ i, x i • hL.eigenvectorBasis i)
        (Matrix.toEuclideanLin (complement L m)⁻¹ (∑ i, x i • hL.eigenvectorBasis i)) =
        ∑ i, (1 - hL.eigenvalues i / m)⁻¹ * (x i) ^ 2 := by
    rw [map_sum]
    simp_rw [map_smul, he, smul_smul, inner_sum, real_inner_smul_right,
      hL.eigenvectorBasis.orthonormal.inner_left_fintype]
    simp only [starRingEnd_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h := hquad (hL.eigenvectorBasis.repr (WithLp.toLp 2 b))
  rw [hL.eigenvectorBasis.sum_repr] at h
  change inner ℝ (WithLp.toLp 2 b) (WithLp.toLp 2 ((complement L m)⁻¹ *ᵥ b)) = _ at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    dotProduct_comm, phaseCoordinates, div_eq_mul_inv, mul_comm] using h

theorem complement_eigenvalues_pos {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2)
    {m : ℝ} (hm : 4 < m) (i : ι) : 0 < 1 - hL.eigenvalues i / m := by
  have hmpos : 0 < m := by linarith
  apply sub_pos.mpr
  apply (div_lt_one hmpos).mpr
  exact (eigenvalues_le_four hL hbound i).trans_lt hm

theorem factor_eq_spectralFactor {L : Matrix ι ι ℝ} (hL : L.IsHermitian)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2)
    (b : ι → ℝ) {m : ℝ} (hm : 4 < m) :
    factor L b m = spectralFactor m hL.eigenvalues (phaseCoordinates hL b) := by
  have hK := complement_posDef hL hbound hm
  have hEig := complement_eigenvalues_pos hL hbound hm
  unfold factor spectralFactor
  rw [complement_inv_quadratic hL b hK hEig, complement_det hL m,
    Real.sqrt_prod _ (fun i _ => (hEig i).le), Finset.prod_inv_distrib]

/-- Deterministic Gaussian determinant--phase estimate for the actual matrix inverse.
The input budgets are derived from the edge set by the forest application. -/
theorem matrix_factor_log_error {L : Matrix ι ι ℝ} (hL : L.PosSemidef)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2)
    (b : ι → ℝ) (m a s : ℝ) (hm : 8 ≤ m)
    (htrace : L.trace = 2 * a) (hphase : ∑ i, b i ^ 2 = 2 * s) :
    0 < factor L b m ∧
      |Real.log (factor L b m) - (a - s) / m| ≤ 8 * (a + s) / m ^ 2 := by
  have hm4 : 4 < m := by linarith
  refine ⟨factor_pos b (complement_posDef hL.isHermitian hbound hm4), ?_⟩
  rw [factor_eq_spectralFactor hL.isHermitian hbound b hm4]
  apply spectralFactor_log_error m a s _ _ hm
  · exact hL.eigenvalues_nonneg
  · exact eigenvalues_le_four hL.isHermitian hbound
  · exact phaseCoordinates_nonneg hL.isHermitian b
  · rw [← htrace, hL.isHermitian.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
  · rw [phaseCoordinates_sum, hphase]

/-- Dimension-only uniform bound, independent of every matrix and endpoint choice. -/
theorem matrix_factor_log_error_uniform {L : Matrix ι ι ℝ} (hL : L.PosSemidef)
    (hbound : ∀ x : ι → ℝ, x ⬝ᵥ L *ᵥ x ≤ 4 * ∑ i, x i ^ 2)
    (b : ι → ℝ) (m a s : ℝ) (hm : 8 ≤ m)
    (htrace : L.trace = 2 * a) (hphase : ∑ i, b i ^ 2 = 2 * s)
    (ha : a ≤ m) (hs : s ≤ m) :
    0 < factor L b m ∧ |Real.log (factor L b m) - (a - s) / m| ≤ 16 / m := by
  obtain ⟨hp, he⟩ := matrix_factor_log_error hL hbound b m a s hm htrace hphase
  refine ⟨hp, he.trans ?_⟩
  have hmpos : 0 < m := by linarith
  calc
    _ ≤ 8 * (m + m) / m ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg m)
      linarith
    _ = _ := by field_simp; ring

/-- The constant zero mode of L becomes eigenvalue exactly 1 of the complement. -/
theorem complement_mulVec_one {L : Matrix ι ι ℝ} (m : ℝ)
    (hzero : L *ᵥ (1 : ι → ℝ) = 0) : complement L m *ᵥ (1 : ι → ℝ) = 1 := by
  simp [complement, Matrix.sub_mulVec, Matrix.smul_mulVec, hzero]

/-- The inverse also acts as identity on the constant mode. No reduced basis is needed. -/
theorem complement_inv_mulVec_one {L : Matrix ι ι ℝ} {m : ℝ}
    (hK : (complement L m).PosDef) (hzero : L *ᵥ (1 : ι → ℝ) = 0) :
    (complement L m)⁻¹ *ᵥ (1 : ι → ℝ) = 1 := by
  have h := congrArg (fun x : ι → ℝ => (complement L m)⁻¹ *ᵥ x)
    (complement_mulVec_one m hzero)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne'),
    Matrix.one_mulVec] at h
  exact h.symm

/-- Zero endpoint sum is the exact finite orthogonality needed for the Gaussian phase. -/
theorem phase_translation_invariant (b x : ι → ℝ) (t : ℝ) (hb : ∑ i, b i = 0) :
    b ⬝ᵥ (x + t • (1 : ι → ℝ)) = b ⬝ᵥ x := by
  rw [dotProduct_add, dotProduct_smul]
  have h : b ⬝ᵥ (1 : ι → ℝ) = 0 := by simpa [dotProduct] using hb
  simp [h]

end ForestGaussian
