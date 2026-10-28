module

public import Tournament.ResolventDerivatives
public import Tournament.HessianDerivatives

/-!
# The actual normalized two-jet of the scalar determinant equation

This file sums the proved matrix resolvent derivatives to obtain the first and
second Fréchet derivatives of `RankOneEquation.phi` itself.
-/

@[expose] public section

open Filter
open scoped Topology Matrix

namespace Tournament.ScalarTwoJet

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum of all matrix entries as a continuous linear functional. -/
noncomputable def sumEntriesCLM : Matrix ι ι ℂ →L[ℂ] ℂ :=
  (show Matrix ι ι ℂ →ₗ[ℂ] ℂ from
    { toFun := fun A => ∑ i, ∑ j, A i j
      map_add' := by intro A B; simp [Finset.sum_add_distrib]
      map_smul' := by intro c A; simp [Finset.mul_sum] }).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem sumEntriesCLM_apply (A : Matrix ι ι ℂ) :
    sumEntriesCLM A = ∑ i, ∑ j, A i j := rfl

noncomputable def affineTotal (d : ℂ) (A : Matrix ι ι ℂ) : ℂ := 1 - d⁻¹ * sumEntriesCLM A

noncomputable def affineTotalFirst (d : ℂ) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  -d⁻¹ • sumEntriesCLM

theorem hasFDerivAt_affineTotal (d : ℂ) (A : Matrix ι ι ℂ) :
    HasFDerivAt (affineTotal d) (affineTotalFirst d) A := by
  have h := (hasFDerivAt_const (1 : ℂ) A).sub (sumEntriesCLM.hasFDerivAt.const_mul d⁻¹)
  convert! h using 1
  ext B
  simp [affineTotalFirst]

/-- The exact rank-one scalar equation is analytic near every invertible pencil. -/
theorem analyticAt_phi (d : ℂ) (C : Matrix ι ι ℂ) (t : ι → ℂ)
    (hu : IsUnit (ResolventDerivatives.pencil C t)) :
    AnalyticAt ℂ (RankOneEquation.phi d C) t := by
  have ha := (sumEntriesCLM.analyticAt _).comp
    (ResolventDerivatives.analyticAt_resolvent C t hu)
  exact analyticAt_const.sub (analyticAt_const.mul ha)

/-- First derivative before row/column-sum normalization. -/
theorem fderiv_phi_zero_raw (d : ℂ) (C : Matrix ι ι ℂ) (v : ι → ℂ)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (RankOneEquation.phi d C) 0 v =
      -d⁻¹ * sumEntriesCLM ((1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹) := by
  have hR := (ResolventDerivatives.analyticAt_resolvent C 0 (by simpa using hu)).differentiableAt.hasFDerivAt
  have hf := (hasFDerivAt_affineTotal d _).comp 0 hR
  have heq := congrArg (fun L => L v) hf.fderiv
  simp only [ContinuousLinearMap.comp_apply] at heq
  rw [ResolventDerivatives.fderiv_resolvent_zero C v hu] at heq
  unfold RankOneEquation.phi
  simpa only [affineTotal, affineTotalFirst, Function.comp_def, smul_apply,
    smul_eq_mul, sumEntriesCLM_apply, RankOneEquation.phi, ResolventDerivatives.pencil] using heq

/-- The actual second derivative before row/column-sum normalization. -/
theorem iterated_fderiv_phi_zero_raw (d : ℂ) (C : Matrix ι ι ℂ) (v w : ι → ℂ)
    (hu : IsUnit (1 - C)) :
    fderiv ℂ (fderiv ℂ (RankOneEquation.phi d C)) 0 v w =
      -d⁻¹ * sumEntriesCLM (
      (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ +
      (1 - C)⁻¹ * Matrix.diagonal w * (1 - C)⁻¹ * Matrix.diagonal v * (1 - C)⁻¹ -
      (1 - C)⁻¹ * Matrix.diagonal (fun i => w i * v i) * (1 - C)⁻¹) := by
  have ha := ResolventDerivatives.analyticAt_resolvent C 0 (by simpa using hu)
  have hg := ha.eventually_analyticAt.mono fun _ h => h.differentiableAt.hasFDerivAt
  have hs := HessianDerivatives.second_chain_rule
    (Filter.Eventually.of_forall (hasFDerivAt_affineTotal d))
    (hasFDerivAt_const (affineTotalFirst d) _)
    hg ha.fderiv.differentiableAt.hasFDerivAt v w
  rw [ResolventDerivatives.iterated_fderiv_resolvent_zero C v w hu] at hs
  unfold RankOneEquation.phi
  simpa only [affineTotal, affineTotalFirst, Function.comp_def,
    zero_apply, zero_add, smul_apply, smul_eq_mul, sumEntriesCLM_apply,
    RankOneEquation.phi, ResolventDerivatives.pencil] using hs

omit [DecidableEq ι] in
/-- Entry sum as a matrix pairing with constant vectors. -/
theorem sumEntries_eq_dot (A : Matrix ι ι ℂ) :
    sumEntriesCLM A = (fun _ => 1) ⬝ᵥ (A *ᵥ (fun _ => 1)) := by
  simp [dotProduct, Matrix.mulVec]

omit [DecidableEq ι] in
theorem sumEntries_mul_left (U A : Matrix ι ι ℂ)
    (hcol : (fun _ => 1) ᵥ* U = fun _ => 1) :
    sumEntriesCLM (U * A) = sumEntriesCLM A := by
  rw [sumEntries_eq_dot, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hcol,
    ← sumEntries_eq_dot]

omit [DecidableEq ι] in
theorem sumEntries_mul_right (U A : Matrix ι ι ℂ)
    (hrow : U *ᵥ (fun _ => 1) = fun _ => 1) :
    sumEntriesCLM (A * U) = sumEntriesCLM A := by
  rw [sumEntries_eq_dot, ← Matrix.mulVec_mulVec, hrow, ← sumEntries_eq_dot]

@[simp] theorem sumEntries_diagonal (v : ι → ℂ) :
    sumEntriesCLM (Matrix.diagonal v) = ∑ i, v i := by
  simp [Matrix.diagonal]

theorem sumEntries_diagonal_sandwich (U : Matrix ι ι ℂ) (v w : ι → ℂ) :
    sumEntriesCLM (Matrix.diagonal v * U * Matrix.diagonal w) = v ⬝ᵥ (U *ᵥ w) := by
  rw [sumEntries_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiag : Matrix.diagonal w *ᵥ (fun _ => 1) = w := by
    ext i; simp [Matrix.mulVec_diagonal]
  rw [hdiag]
  simp [dotProduct, Matrix.mulVec_diagonal]

omit [DecidableEq ι] in
theorem sumEntries_outer (U A : Matrix ι ι ℂ)
    (hrow : U *ᵥ (fun _ => 1) = fun _ => 1)
    (hcol : (fun _ => 1) ᵥ* U = fun _ => 1) :
    sumEntriesCLM (U * A * U) = sumEntriesCLM A := by
  rw [sumEntries_mul_right U _ hrow, sumEntries_mul_left U _ hcol]

theorem sumEntries_two_projectors (U : Matrix ι ι ℂ) (v w : ι → ℂ)
    (hrow : U *ᵥ (fun _ => 1) = fun _ => 1)
    (hcol : (fun _ => 1) ᵥ* U = fun _ => 1) :
    sumEntriesCLM (U * Matrix.diagonal v * U * Matrix.diagonal w * U) =
      v ⬝ᵥ (U *ᵥ w) := by
  have he := sumEntries_outer U (Matrix.diagonal v * U * Matrix.diagonal w) hrow hcol
  rw [sumEntries_diagonal_sandwich] at he
  simpa only [Matrix.mul_assoc] using he

/-- The first normalized scalar derivative, with the two fixed-ones identities
made explicit rather than silently assumed from regularity. -/
theorem fderiv_phi_zero (d : ℂ) (C : Matrix ι ι ℂ) (v : ι → ℂ)
    (hu : IsUnit (1 - C))
    (hrow : (1 - C)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1)
    (hcol : (fun _ => 1) ᵥ* (1 - C)⁻¹ = fun _ => 1) :
    fderiv ℂ (RankOneEquation.phi d C) 0 v = -(∑ i, v i) / d := by
  rw [fderiv_phi_zero_raw d C v hu, sumEntries_mul_right _ _ hrow,
    sumEntries_mul_left _ _ hcol, sumEntries_diagonal]
  simp [div_eq_mul_inv, mul_comm]

/-- The actual normalized scalar Hessian is minus the bilinear form associated
with `U + Uᵀ - I`, divided by `d`. -/
theorem iterated_fderiv_phi_zero (d : ℂ) (C : Matrix ι ι ℂ) (v w : ι → ℂ)
    (hu : IsUnit (1 - C))
    (hrow : (1 - C)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1)
    (hcol : (fun _ => 1) ᵥ* (1 - C)⁻¹ = fun _ => 1) :
    fderiv ℂ (fderiv ℂ (RankOneEquation.phi d C)) 0 v w =
      -(v ⬝ᵥ (((1 - C)⁻¹ + (1 - C)⁻¹ᵀ - 1) *ᵥ w)) / d := by
  rw [iterated_fderiv_phi_zero_raw d C v w hu, map_sub, map_add]
  rw [sumEntries_two_projectors _ v w hrow hcol,
    sumEntries_two_projectors _ w v hrow hcol, sumEntries_outer _ _ hrow hcol,
    sumEntries_diagonal]
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_add, Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, mul_comm (w _) (v _), div_eq_mul_inv, neg_mul]
  ring

omit [DecidableEq ι] in
/-- Zero row sums of a real matrix persist under complexification. -/
theorem complexification_mulVec_one_zero (C : Matrix ι ι ℝ)
    (hC : C *ᵥ (fun _ => 1) = 0) :
    C.map Complex.ofReal *ᵥ (fun _ => 1) = 0 := by
  ext i
  have h := Complex.ofRealHom.map_mulVec C (fun _ => 1) i
  rw [hC] at h
  simpa [Function.comp_def, Complex.ofRealHom] using h.symm

omit [DecidableEq ι] in
/-- Skew-symmetry turns zero row sums into zero column sums, also after casting. -/
theorem complexification_one_vecMul_zero (C : Matrix ι ι ℝ)
    (hskew : Cᵀ = -C) (hC : C *ᵥ (fun _ => 1) = 0) :
    (fun _ => 1) ᵥ* C.map Complex.ofReal = 0 := by
  have hcol : (fun _ => 1) ᵥ* C = 0 := by
    rw [← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec, hC, neg_zero]
  ext i
  have h := Complex.ofRealHom.map_vecMul C (fun _ => 1) i
  rw [hcol] at h
  simpa [Function.comp_def, Complex.ofRealHom] using h.symm

/-- The normalization of the inverse follows from the actual real skew matrix,
not from an additional assumption on an abstract two-jet. -/
theorem complex_skew_inverse_fixes_one (C : Matrix ι ι ℝ)
    (hskew : Cᵀ = -C) (hC : C *ᵥ (fun _ => 1) = 0) :
    ((1 - C.map Complex.ofReal)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1) ∧
    ((fun _ => 1) ᵥ* (1 - C.map Complex.ofReal)⁻¹ = fun _ => 1) := by
  have hu := RankOneEquation.one_sub_complex_skew_isUnit C hskew
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  exact ⟨RankOneEquation.inv_one_sub_mulVec_one _ (complexification_mulVec_one_zero C hC) hd,
    RankOneEquation.one_vecMul_inv_one_sub _ (complexification_one_vecMul_zero C hskew hC) hd⟩

/-- The genuine scalar equation's normalized first derivative for real regular
skew data. No invertibility or derivative assumptions remain. -/
theorem fderiv_phi_zero_real_skew (d : ℂ) (C : Matrix ι ι ℝ) (v : ι → ℂ)
    (hskew : Cᵀ = -C) (hC : C *ᵥ (fun _ => 1) = 0) :
    fderiv ℂ (RankOneEquation.phi d (C.map Complex.ofReal)) 0 v = -(∑ i, v i) / d := by
  obtain ⟨hr, hc⟩ := complex_skew_inverse_fixes_one C hskew hC
  exact fderiv_phi_zero d _ v (RankOneEquation.one_sub_complex_skew_isUnit C hskew) hr hc

/-- The second derivative of the genuine scalar equation is the paper's real
rational resolvent form after complexification. Only real skew-symmetry and
zero row sums are assumed; analyticity and the inverse two-jet were proved above. -/
theorem iterated_fderiv_phi_zero_real_skew (d : ℂ) (C : Matrix ι ι ℝ) (v w : ι → ℂ)
    (hskew : Cᵀ = -C) (hC : C *ᵥ (fun _ => 1) = 0) :
    fderiv ℂ (fderiv ℂ (RankOneEquation.phi d (C.map Complex.ofReal))) 0 v w =
      -(v ⬝ᵥ (((HessianAlgebra.resolvent C).map Complex.ofReal) *ᵥ w)) / d := by
  obtain ⟨hr, hc⟩ := complex_skew_inverse_fixes_one C hskew hC
  rw [iterated_fderiv_phi_zero d _ v w
    (RankOneEquation.one_sub_complex_skew_isUnit C hskew) hr hc,
    HessianAlgebra.complexified_resolvent_identity C hskew]

/-- Local analyticity at zero also requires no separate inverse hypothesis. -/
theorem analyticAt_phi_real_skew (d : ℂ) (C : Matrix ι ι ℝ) (hskew : Cᵀ = -C) :
    AnalyticAt ℂ (RankOneEquation.phi d (C.map Complex.ofReal)) 0 :=
  analyticAt_phi d _ 0 (by
    simpa using RankOneEquation.one_sub_complex_skew_isUnit C hskew)

end Tournament.ScalarTwoJet
