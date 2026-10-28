module

public import Tournament.RankOneEquation
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NoncommRing

/-!
# Actual derivatives of the matrix resolvent

Inverse differentiation is proved for normed algebras first, then applied to the
finite matrix `diag(exp(-tᵢ)) - C`. The conclusions use actual Fréchet derivatives.
-/

@[expose] public section

open Filter
open scoped Topology Matrix

namespace Tournament.ResolventDerivatives

set_option backward.isDefEq.respectTransparency false

section GeneralInverse

variable {𝕜 X A : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A]

/-- The derivative of inversion composed with a differentiable algebra-valued map. -/
theorem hasFDerivAt_inverse_comp {M : X → A} {M' : X →L[𝕜] A} {x : X}
    (hM : HasFDerivAt M M' x) (hu : IsUnit (M x)) :
    HasFDerivAt (fun y => Ring.inverse (M y))
      ((-ContinuousLinearMap.mulLeftRight 𝕜 A (Ring.inverse (M x))
        (Ring.inverse (M x))).comp M') x := by
  rcases hu with ⟨u, hu⟩
  have hi := hasFDerivAt_ringInverse (𝕜 := 𝕜) u
  rw [← Ring.inverse_unit, hu] at hi
  exact hi.comp x hM

/-- Pointwise first derivative of an algebra inverse. -/
theorem fderiv_inverse_comp {M : X → A} {M' : X →L[𝕜] A} {x : X}
    (hM : HasFDerivAt M M' x) (hu : IsUnit (M x)) (v : X) :
    fderiv 𝕜 (fun y => Ring.inverse (M y)) x v =
      -(Ring.inverse (M x) * M' v * Ring.inverse (M x)) := by
  rw [(hasFDerivAt_inverse_comp hM hu).fderiv]
  rfl

/-- Second inverse chain rule in two directions. The derivative hypotheses concern
`M` and its derivative field; no desired derivative of its inverse is assumed. -/
theorem second_fderiv_inverse_comp
    {M : X → A} {M' : X → X →L[𝕜] A} {x : X} {w : X}
    {Mw' : X →L[𝕜] A}
    (hM : ∀ᶠ y in 𝓝 x, HasFDerivAt M (M' y) y)
    (hMw : HasFDerivAt (fun y => M' y w) Mw' x)
    (hu : IsUnit (M x)) (v : X) :
    fderiv 𝕜 (fun y => fderiv 𝕜 (fun z => Ring.inverse (M z)) y w) x v =
      Ring.inverse (M x) * M' x v * Ring.inverse (M x) * M' x w * Ring.inverse (M x) +
      Ring.inverse (M x) * M' x w * Ring.inverse (M x) * M' x v * Ring.inverse (M x) -
      Ring.inverse (M x) * Mw' v * Ring.inverse (M x) := by
  have hR := hasFDerivAt_inverse_comp hM.self_of_nhds hu
  have hprod := ((hR.mul' hMw).mul' hR).neg
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (M y) :=
    hM.self_of_nhds.continuousAt (Units.isOpen.mem_nhds hu)
  have heq : (fun y => fderiv 𝕜 (fun z => Ring.inverse (M z)) y w) =ᶠ[𝓝 x]
      fun y => -(Ring.inverse (M y) * M' y w * Ring.inverse (M y)) := by
    filter_upwards [hM, hunit] with y hMy huy
    exact fderiv_inverse_comp hMy huy w
  rw [(hprod.congr_of_eventuallyEq heq).fderiv]
  simp only [neg_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    smul_apply, smul_eq_mul, op_smul_eq_mul, Pi.mul_apply]
  noncomm_ring

end GeneralInverse

section MatrixResolvent

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix whose inverse occurs in the rank-one determinant reduction. -/
noncomputable def pencil (C : Matrix ι ι ℂ) (t : ι → ℂ) : Matrix ι ι ℂ :=
  RankOneEquation.M C t

/-- Continuous linear diagonal embedding, with the operator matrix norm. -/
noncomputable def diagonalCLM : (ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
  (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap

@[simp] theorem diagonalCLM_apply (v : ι → ℂ) :
    diagonalCLM v = Matrix.diagonal v := rfl

/-- Actual first derivative field of the exponential diagonal pencil. -/
noncomputable def pencilFirst (t : ι → ℂ) : (ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
  diagonalCLM.comp (ContinuousLinearMap.pi fun i =>
    Complex.exp (-t i) • -(ContinuousLinearMap.proj i))

@[simp] theorem pencilFirst_apply (t v : ι → ℂ) :
    pencilFirst t v = Matrix.diagonal (fun i => -Complex.exp (-t i) * v i) := by
  simp [pencilFirst, ContinuousLinearMap.comp_apply, neg_mul]

/-- Derivative of the first derivative field after application to a fixed vector. -/
noncomputable def pencilSecondApply (t w : ι → ℂ) :
    (ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
  diagonalCLM.comp (ContinuousLinearMap.pi fun i =>
    (Complex.exp (-t i) * w i) • ContinuousLinearMap.proj i)

@[simp] theorem pencilSecondApply_apply (t w v : ι → ℂ) :
    pencilSecondApply t w v =
      Matrix.diagonal (fun i => Complex.exp (-t i) * w i * v i) := by
  simp [pencilSecondApply, ContinuousLinearMap.comp_apply]

theorem hasFDerivAt_pencil (C : Matrix ι ι ℂ) (t : ι → ℂ) :
    HasFDerivAt (pencil C) (pencilFirst t) t := by
  have h := hasFDerivAt_pi.mpr fun i : ι =>
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := t) |>.neg).cexp
  exact (diagonalCLM.hasFDerivAt.comp t h).sub_const C

theorem hasFDerivAt_pencilFirst_apply (t w : ι → ℂ) :
    HasFDerivAt (fun y => pencilFirst y w) (pencilSecondApply t w) t := by
  have h := hasFDerivAt_pi.mpr fun i : ι =>
    (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt (x := t) |>.neg).cexp.neg).mul_const (w i)
  convert! diagonalCLM.hasFDerivAt.comp t h using 1
  · ext y i j
    simp [pencilFirst_apply]
  · ext v i j
    simp [pencilSecondApply_apply, ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm]

theorem analyticAt_pencil (C : Matrix ι ι ℂ) (t : ι → ℂ) :
    AnalyticAt ℂ (pencil C) t := by
  have h := AnalyticAt.pi fun i : ι =>
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt t |>.neg).cexp'
  exact ((diagonalCLM.analyticAt _).comp h).sub analyticAt_const

/-- Local analyticity of the genuine inverse pencil at any invertible point. -/
theorem analyticAt_resolvent (C : Matrix ι ι ℂ) (t : ι → ℂ)
    (hu : IsUnit (pencil C t)) :
    AnalyticAt ℂ (fun y => (pencil C y)⁻¹) t := by
  have h := (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp (analyticAt_pencil C t)
  simpa! only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using h

/-- The inverse pencil's actual first derivative. -/
theorem fderiv_resolvent (C : Matrix ι ι ℂ) (t v : ι → ℂ)
    (hu : IsUnit (pencil C t)) :
    fderiv ℂ (fun y => (pencil C y)⁻¹) t v =
      -(pencil C t)⁻¹ * pencilFirst t v * (pencil C t)⁻¹ := by
  simpa! only [Matrix.nonsing_inv_eq_ringInverse, neg_mul] using
    fderiv_inverse_comp (hasFDerivAt_pencil C t) hu v

/-- The actual mixed second directional derivative of the inverse pencil. -/
theorem second_fderiv_resolvent (C : Matrix ι ι ℂ) (t v w : ι → ℂ)
    (hu : IsUnit (pencil C t)) :
    fderiv ℂ (fun y => fderiv ℂ (fun z => (pencil C z)⁻¹) y w) t v =
      (pencil C t)⁻¹ * pencilFirst t v * (pencil C t)⁻¹ * pencilFirst t w * (pencil C t)⁻¹ +
      (pencil C t)⁻¹ * pencilFirst t w * (pencil C t)⁻¹ * pencilFirst t v * (pencil C t)⁻¹ -
      (pencil C t)⁻¹ * pencilSecondApply t w v * (pencil C t)⁻¹ := by
  simpa! only [Matrix.nonsing_inv_eq_ringInverse] using
    second_fderiv_inverse_comp (Filter.Eventually.of_forall (hasFDerivAt_pencil C))
      (hasFDerivAt_pencilFirst_apply t w) hu v

omit [Fintype ι] in
@[simp] theorem pencil_zero (C : Matrix ι ι ℂ) : pencil C 0 = 1 - C :=
  RankOneEquation.M_zero C

@[simp] theorem pencilFirst_zero_apply (v : ι → ℂ) :
    pencilFirst 0 v = -Matrix.diagonal v := by
  rw [pencilFirst_apply]
  simp [← Matrix.diagonal_neg]

@[simp] theorem pencilSecondApply_zero_apply (w v : ι → ℂ) :
    pencilSecondApply 0 w v = Matrix.diagonal (fun i => w i * v i) := by
  simp [pencilSecondApply_apply]

/-- The first resolvent derivative at the expansion point, in arbitrary directions. -/
theorem fderiv_resolvent_zero (C : Matrix ι ι ℂ) (v : ι → ℂ)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fun y => (pencil C y)⁻¹) 0 v =
      (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ := by
  simpa only [pencil_zero, pencilFirst_zero_apply, neg_mul, mul_neg, neg_neg] using
    fderiv_resolvent C 0 v (by simpa using hu)

/-- Mixed second resolvent derivatives at zero, in arbitrary directions. -/
theorem second_fderiv_resolvent_zero (C : Matrix ι ι ℂ) (v w : ι → ℂ)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fun y => fderiv ℂ (fun z => (pencil C z)⁻¹) y w) 0 v =
      (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ +
      (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ -
      (1 - C)⁻¹ * Matrix.diagonal (fun i => w i * v i) * (1 - C)⁻¹ := by
  simpa only [pencil_zero, pencilFirst_zero_apply, pencilSecondApply_zero_apply,
    neg_mul, mul_neg, neg_neg] using
    second_fderiv_resolvent C 0 v w (by simpa using hu)

/-- The same formula for the actual iterated Fréchet derivative, not just
successive scalar-direction differentiation. Analyticity supplies the derivative
of the full first-derivative field. -/
theorem iterated_fderiv_resolvent_zero (C : Matrix ι ι ℂ) (v w : ι → ℂ)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fderiv ℂ (fun z => (pencil C z)⁻¹)) 0 v w =
      (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ +
      (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ -
      (1 - C)⁻¹ * Matrix.diagonal (fun i => w i * v i) * (1 - C)⁻¹ := by
  have ha := (analyticAt_resolvent C 0 (by simpa using hu)).fderiv.differentiableAt.hasFDerivAt
  have he := (ha.clm_apply (hasFDerivAt_const w 0)).fderiv
  have hv := congrArg (fun L => L v) he
  have hs := second_fderiv_resolvent_zero C v w hu
  rw [hv] at hs
  simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] using hs

/-- The matrix coordinate projector `Fⱼ`. -/
def coordinateProjector (j : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (Pi.single j 1)

/-- `Rⱼ(0) = U Fⱼ U`, as an actual Fréchet derivative. -/
theorem fderiv_resolvent_coordinate (C : Matrix ι ι ℂ) (j : ι)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fun y => (pencil C y)⁻¹) 0 (Pi.single j 1) =
      (1 - C)⁻¹ * coordinateProjector j * (1 - C)⁻¹ :=
  fderiv_resolvent_zero C _ hu

/-- `Rⱼₖ(0) = U Fₖ U Fⱼ U + U Fⱼ U Fₖ U − δⱼₖ U Fⱼ U`.
The Kronecker term is written as an `if`, avoiding a scalar/matrix coercion. -/
theorem iterated_fderiv_resolvent_coordinate (C : Matrix ι ι ℂ) (j k : ι)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fderiv ℂ (fun z => (pencil C z)⁻¹)) 0 (Pi.single k 1) (Pi.single j 1) =
      (1 - C)⁻¹ * coordinateProjector k * (1 - C)⁻¹ * coordinateProjector j * (1 - C)⁻¹ +
      (1 - C)⁻¹ * coordinateProjector j * (1 - C)⁻¹ * coordinateProjector k * (1 - C)⁻¹ -
      (if j = k then (1 - C)⁻¹ * coordinateProjector j * (1 - C)⁻¹ else 0) := by
  rw [iterated_fderiv_resolvent_zero C _ _ hu]
  congr 1
  by_cases h : j = k
  · subst k
    have hsq : (fun i => (Pi.single j 1 : ι → ℂ) i * (Pi.single j 1 : ι → ℂ) i) =
        (Pi.single j 1 : ι → ℂ) := by
      ext i
      by_cases hi : i = j <;> simp [hi]
    simp [hsq, coordinateProjector]
  · have hz : (fun i => (Pi.single j 1 : ι → ℂ) i * (Pi.single k 1 : ι → ℂ) i) = 0 := by
      ext i
      by_cases hj : i = j
      · subst i; simp [h]
      · simp [Pi.single_apply, hj]
    simp [h, hz]

/-- Real skew-symmetry is sufficient for every inverse used at the base point. -/
theorem one_sub_complex_skew_isUnit (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    IsUnit (1 - C.map Complex.ofReal) := by
  exact RankOneEquation.one_sub_complex_skew_isUnit C hC

end MatrixResolvent

end Tournament.ResolventDerivatives
