module

public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# The differential bridge in the Wormald Hessian calculation

This file verifies actual first and second Fréchet derivatives, rather than defining
an alleged Hessian to be the desired matrix. Theorems are local: derivatives need
only exist on a neighbourhood of the expansion point.

The generic chain rule and implicit-graph identity below implement §§3.4–3.6 of
`04_wormald.zh.md` (the same calculation occurs in §9 of the combined manuscript).
The last-coordinate quotient lemma proves local analytic solvability for an affine
constraint, provided its two coefficient functions are analytic and the coefficient
of the last coordinate is nonzero. Instantiation with the manuscript's determinant,
and verification of its Schur-complement two-jet, are separate obligations; this file
does not claim these hypotheses have already been established for every tournament.
-/

public section

open Filter
open scoped Topology

namespace Tournament.HessianDerivatives

section ChainRule

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The second chain rule, with explicit local first-derivative fields.
Both sides concern the actual iterated `fderiv`. -/
theorem second_chain_rule
    {f : Y → Z} {f₁ : Y → Y →L[𝕜] Z}
    {f₂ : Y →L[𝕜] Y →L[𝕜] Z}
    {g : X → Y} {g₁ : X → X →L[𝕜] Y}
    {g₂ : X →L[𝕜] X →L[𝕜] Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 (g x), HasFDerivAt f (f₁ y) y)
    (hf₂ : HasFDerivAt f₁ f₂ (g x))
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ x) (v w : X) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ g)) x v w =
      f₂ (g₁ x v) (g₁ x w) + f₁ (g x) (g₂ v w) := by
  have hgx := hg.self_of_nhds
  have hc := (hf₂.comp x hgx).clm_comp hg₂
  have heq : fderiv 𝕜 (f ∘ g) =ᶠ[𝓝 x]
      fun y => (f₁ (g y)).comp (g₁ y) := by
    filter_upwards [hg, hgx.continuousAt hf] with y hgy hfy
    exact (hfy.comp y hgy).fderiv
  rw [(hc.congr_of_eventuallyEq heq).fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, add_comm]

/-- A twice differentiable parametrization of a local zero set has vanishing
second derivative of the constraint. This proves the second-order implicit
identity from the function equation, not from a postulated Hessian equation. -/
theorem implicit_second_identity
    {f : Y → Z} {f₁ : Y → Y →L[𝕜] Z}
    {f₂ : Y →L[𝕜] Y →L[𝕜] Z}
    {g : X → Y} {g₁ : X → X →L[𝕜] Y}
    {g₂ : X →L[𝕜] X →L[𝕜] Y} {x : X}
    (hf : ∀ᶠ y in 𝓝 (g x), HasFDerivAt f (f₁ y) y)
    (hf₂ : HasFDerivAt f₁ f₂ (g x))
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ x)
    (hzero : (f ∘ g) =ᶠ[𝓝 x] fun _ => 0) (v w : X) :
    f₂ (g₁ x v) (g₁ x w) + f₁ (g x) (g₂ v w) = 0 := by
  rw [← second_chain_rule hf hf₂ hg hg₂ v w,
    hzero.fderiv.fderiv_eq]
  simp

end ChainRule

section Schur

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The two surviving terms in the second derivative of `b R c` when `b = c = 0`.

The row `b`, inverse block `R`, and column `c` are functions into spaces of
continuous linear maps. No inverse differentiation formula is needed in the
conclusion: all terms involving a derivative of `R` cancel. The result uses
actual mixed directional Fréchet derivatives and is valid for rectangular blocks. -/
theorem schur_product_second_at_zero
    {b : X → E →L[𝕜] 𝕜} {b₁ : X → X →L[𝕜] E →L[𝕜] 𝕜}
    {b₂ : X →L[𝕜] X →L[𝕜] E →L[𝕜] 𝕜}
    {R : X → F →L[𝕜] E} {R₁ : X → X →L[𝕜] F →L[𝕜] E}
    {R₂ : X →L[𝕜] X →L[𝕜] F →L[𝕜] E}
    {c : X → F} {c₁ : X → X →L[𝕜] F} {c₂ : X →L[𝕜] X →L[𝕜] F}
    {x : X}
    (hb : ∀ᶠ y in 𝓝 x, HasFDerivAt b (b₁ y) y)
    (hb₂ : HasFDerivAt b₁ b₂ x)
    (hR : ∀ᶠ y in 𝓝 x, HasFDerivAt R (R₁ y) y)
    (hR₂ : HasFDerivAt R₁ R₂ x)
    (hc : ∀ᶠ y in 𝓝 x, HasFDerivAt c (c₁ y) y)
    (hc₂ : HasFDerivAt c₁ c₂ x)
    (hb0 : b x = 0) (hc0 : c x = 0) (v w : X) :
    fderiv 𝕜 (fun y => fderiv 𝕜 (fun z => b z (R z (c z))) y w) x v =
      b₁ x v (R x (c₁ x w)) + b₁ x w (R x (c₁ x v)) := by
  have hbw := hb₂.clm_apply (hasFDerivAt_const w x)
  have hRw := hR₂.clm_apply (hasFDerivAt_const w x)
  have hcw := hc₂.clm_apply (hasFDerivAt_const w x)
  have hRc := hR.self_of_nhds.clm_apply hc.self_of_nhds
  have hfirst := hbw.clm_apply hRc
  have hsecond := hb.self_of_nhds.clm_apply
    ((hRw.clm_apply hc.self_of_nhds).add (hR.self_of_nhds.clm_apply hcw))
  have hsum := hfirst.add hsecond
  have heq : (fun y => fderiv 𝕜 (fun z => b z (R z (c z))) y w) =ᶠ[𝓝 x]
      fun y => b₁ y w (R y (c y)) + b y (R₁ y w (c y) + R y (c₁ y w)) := by
    filter_upwards [hb, hR, hc] with y hby hRy hcy
    rw [(hby.clm_apply (hRy.clm_apply hcy)).fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_comm]
  rw [(hsum.congr_of_eventuallyEq heq).fderiv]
  simp [hb0, hc0, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm]

end Schur

section Graph

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Derivative of the graph map `x ↦ (x, g x)`. -/
def graphDeriv (A : X →L[𝕜] 𝕜) : X →L[𝕜] X × 𝕜 :=
  ContinuousLinearMap.inl 𝕜 X 𝕜 +
    (ContinuousLinearMap.inr 𝕜 X 𝕜).comp A

@[simp] theorem graphDeriv_apply (A : X →L[𝕜] 𝕜) (v : X) :
    graphDeriv A v = (v, A v) := by
  simp [graphDeriv]

/-- Second derivative of the graph map: only the last coordinate varies. -/
noncomputable def graphSecond (B : X →L[𝕜] X →L[𝕜] 𝕜) :
    X →L[𝕜] X →L[𝕜] X × 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 X 𝕜 (X × 𝕜)
    (ContinuousLinearMap.inr 𝕜 X 𝕜)).comp B

@[simp] theorem graphSecond_apply (B : X →L[𝕜] X →L[𝕜] 𝕜) (v w : X) :
    graphSecond B v w = (0, B v w) := by
  simp [graphSecond, ContinuousLinearMap.compL_apply]

theorem hasFDerivAt_graph
    {g : X → 𝕜} {A : X →L[𝕜] 𝕜} {x : X}
    (h : HasFDerivAt g A x) :
    HasFDerivAt (fun y => (y, g y)) (graphDeriv A) x := by
  have heq : graphDeriv A = (ContinuousLinearMap.id 𝕜 X).prod A := by
    ext v <;> simp
  simpa only [heq, id_eq] using (hasFDerivAt_id x).prodMk h

theorem hasFDerivAt_graphDeriv
    {g₁ : X → X →L[𝕜] 𝕜} {B : X →L[𝕜] X →L[𝕜] 𝕜} {x : X}
    (h : HasFDerivAt g₁ B x) :
    HasFDerivAt (fun y => graphDeriv (g₁ y)) (graphSecond B) x := by
  have hc := ((ContinuousLinearMap.compL 𝕜 X 𝕜 (X × 𝕜)
    (ContinuousLinearMap.inr 𝕜 X 𝕜)).hasFDerivAt.comp x h)
  convert! (hasFDerivAt_const (ContinuousLinearMap.inl 𝕜 X 𝕜) x).add hc using 1
  simp [graphSecond]

/-- The genuine second-order implicit-graph equation. In coordinates this is
`ψ_jk + ψ_jd g_k + ψ_dk g_j + ψ_dd g_j g_k + ψ_d g_jk = 0`. -/
theorem implicit_graph_second
    {ψ : X × 𝕜 → 𝕜} {ψ₁ : X × 𝕜 → (X × 𝕜) →L[𝕜] 𝕜}
    {ψ₂ : (X × 𝕜) →L[𝕜] (X × 𝕜) →L[𝕜] 𝕜}
    {g : X → 𝕜} {g₁ : X → X →L[𝕜] 𝕜}
    {g₂ : X →L[𝕜] X →L[𝕜] 𝕜} {x : X}
    (hψ : ∀ᶠ y in 𝓝 (x, g x), HasFDerivAt ψ (ψ₁ y) y)
    (hψ₂ : HasFDerivAt ψ₁ ψ₂ (x, g x))
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ x)
    (hzero : (fun y => ψ (y, g y)) =ᶠ[𝓝 x] fun _ => 0) (v w : X) :
    ψ₂ (v, g₁ x v) (w, g₁ x w) + ψ₁ (x, g x) (0, g₂ v w) = 0 := by
  have hgraph : ∀ᶠ y in 𝓝 x,
      HasFDerivAt (fun z => (z, g z)) (graphDeriv (g₁ y)) y :=
    hg.mono fun _ h => hasFDerivAt_graph h
  simpa using implicit_second_identity (g := fun y => (y, g y))
    (g₁ := fun y => graphDeriv (g₁ y)) (g₂ := graphSecond g₂) hψ hψ₂ hgraph
    (hasFDerivAt_graphDeriv hg₂) hzero v w

/-- First implicit derivative, proved from the local zero-set identity. -/
theorem implicit_graph_first
    {ψ : X × 𝕜 → 𝕜} {ψ₁ : (X × 𝕜) →L[𝕜] 𝕜}
    {g : X → 𝕜} {g₁ : X →L[𝕜] 𝕜} {x : X}
    (hψ : HasFDerivAt ψ ψ₁ (x, g x))
    (hg : HasFDerivAt g g₁ x)
    (hzero : (fun y => ψ (y, g y)) =ᶠ[𝓝 x] fun _ => 0) (v : X) :
    ψ₁ (v, g₁ v) = 0 := by
  have hc := hψ.comp x (hasFDerivAt_graph hg)
  have hz : HasFDerivAt (fun y => ψ (y, g y)) 0 x :=
    (hasFDerivAt_const (𝕜 := 𝕜) (0 : 𝕜) x).congr_of_eventuallyEq hzero
  have heq := congrArg (fun A : X →L[𝕜] 𝕜 => A v) (hc.unique hz)
  simpa using heq

/-- The local derivative field is the actual derivative, also at second order. -/
theorem second_fderiv_eq
    {g : X → 𝕜} {g₁ : X → X →L[𝕜] 𝕜}
    {g₂ : X →L[𝕜] X →L[𝕜] 𝕜} {x : X}
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ x) :
    fderiv 𝕜 (fderiv 𝕜 g) x = g₂ := by
  exact (hg₂.congr_of_eventuallyEq (hg.mono fun _ h => h.fderiv)).fderiv

/-- The implicit Hessian formula with the manuscript's normalization.

Here `ℓ` is the sum of the first coordinates, and `Q` is the bilinear form
computed by the Schur-complement calculation. The hypotheses about `ψ₁` and
`ψ₂` are explicit analytic obligations, not definitions of the Hessian of `g`.
The conclusion concerns the actual iterated Fréchet derivative of `g`. -/
theorem implicit_hessian_of_normalized_two_jet
    {ψ : X × 𝕜 → 𝕜} {ψ₁ : X × 𝕜 → (X × 𝕜) →L[𝕜] 𝕜}
    {ψ₂ : (X × 𝕜) →L[𝕜] (X × 𝕜) →L[𝕜] 𝕜}
    {g : X → 𝕜} {g₁ : X → X →L[𝕜] 𝕜}
    {g₂ : X →L[𝕜] X →L[𝕜] 𝕜} {x : X}
    (ℓ : X →L[𝕜] 𝕜) (Q : (X × 𝕜) →L[𝕜] (X × 𝕜) →L[𝕜] 𝕜)
    {d : 𝕜} (hd : d ≠ 0)
    (hψ : ∀ᶠ y in 𝓝 (x, g x), HasFDerivAt ψ (ψ₁ y) y)
    (hψ₂ : HasFDerivAt ψ₁ ψ₂ (x, g x))
    (hg : ∀ᶠ y in 𝓝 x, HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ x)
    (hzero : (fun y => ψ (y, g y)) =ᶠ[𝓝 x] fun _ => 0)
    (hfirst : ∀ z, ψ₁ (x, g x) z = -(ℓ z.1 + z.2) / d)
    (hsecond : ∀ z t, ψ₂ z t = -Q z t / d) (v w : X) :
    fderiv 𝕜 (fderiv 𝕜 g) x v w = -Q (v, -ℓ v) (w, -ℓ w) := by
  have hg₁ : ∀ u, g₁ x u = -ℓ u := by
    intro u
    have h := implicit_graph_first hψ.self_of_nhds hg.self_of_nhds hzero u
    rw [hfirst] at h
    have hz : ℓ u + g₁ x u = 0 := neg_eq_zero.mp ((div_eq_zero_iff.mp h).resolve_right hd)
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hz)
  have h := implicit_graph_second hψ hψ₂ hg hg₂ hzero v w
  rw [hsecond, hfirst, hg₁ v, hg₁ w] at h
  have hz : -(Q (v, -ℓ v) (w, -ℓ w) + g₂ v w) / d = 0 := by
    simpa [neg_add, add_div, add_comm] using h
  have heq : g₂ v w = -Q (v, -ℓ v) (w, -ℓ w) := by
    apply (eq_neg_iff_add_eq_zero).2
    simpa [add_comm] using neg_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hd)
  rw [second_fderiv_eq hg hg₂]
  exact heq

end Graph

section Angle

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Multiplying both directions by `i` changes the complex Hessian's sign.
This verifies the angle-variable step with actual derivatives, including an
arbitrary additive logarithm-branch constant. -/
theorem second_complex_angle
    {g : X → ℂ} {g₁ : X → X →L[ℂ] ℂ}
    {g₂ : X →L[ℂ] X →L[ℂ] ℂ}
    (hg : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ 0) (c : ℂ) (v w : X) :
    fderiv ℂ (fderiv ℂ (fun y => c + g (Complex.I • y))) 0 v w = -g₂ v w := by
  let A : X →L[ℂ] X := Complex.I • ContinuousLinearMap.id ℂ X
  have hgA : ∀ᶠ y in 𝓝 (A 0), HasFDerivAt g (g₁ y) y := by simpa using hg
  have hg₂A : HasFDerivAt g₁ g₂ (A 0) := by simpa using hg₂
  have hA : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt A A y :=
    Filter.Eventually.of_forall fun _ => A.hasFDerivAt
  have hc := second_chain_rule hgA hg₂A hA (hasFDerivAt_const A (0 : X)) v w
  have heq : fderiv ℂ (fun y => c + g (Complex.I • y)) =
      fderiv ℂ (g ∘ A) := by
    funext y
    exact fderiv_const_add c
  rw [heq]
  simpa [A, Function.comp_def, smul_smul, ← mul_assoc, Complex.I_mul_I] using hc

/-- The angle sign change for an actual real parameter space. `L` embeds real
coordinate directions into the complex logarithmic-coordinate space. Thus this
statement applies directly to the real-variable angle function in the manuscript,
not just to its holomorphic extension. -/
theorem second_real_angle
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
    {g : X → ℂ} {g₁ : X → X →L[ℂ] ℂ}
    {g₂ : X →L[ℂ] X →L[ℂ] ℂ}
    (hg : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ 0) (L : Y →L[ℝ] X) (c : ℂ) (v w : Y) :
    fderiv ℝ (fderiv ℝ (fun y => c + g (Complex.I • L y))) 0 v w =
      -g₂ (L v) (L w) := by
  let r : (X →L[ℂ] ℂ) →L[ℝ] X →L[ℝ] ℂ :=
    ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ
  let A : Y →L[ℝ] X := Complex.I • L
  let g₂r : X →L[ℝ] X →L[ℝ] ℂ := r.comp (g₂.restrictScalars ℝ)
  have hgR : ∀ᶠ y in 𝓝 (A 0), HasFDerivAt g ((g₁ y).restrictScalars ℝ) y := by
    simpa using hg.mono (fun _ h => h.restrictScalars ℝ)
  have hg₂R : HasFDerivAt (fun y => (g₁ y).restrictScalars ℝ) g₂r (A 0) := by
    simpa [g₂r, r, Function.comp_def] using r.hasFDerivAt.comp 0 (hg₂.restrictScalars ℝ)
  have hA : ∀ᶠ y in 𝓝 (0 : Y), HasFDerivAt A A y :=
    Filter.Eventually.of_forall fun _ => A.hasFDerivAt
  have hc := second_chain_rule hgR hg₂R hA (hasFDerivAt_const A (0 : Y)) v w
  have heq : fderiv ℝ (fun y => c + g (Complex.I • L y)) =
      fderiv ℝ (g ∘ A) := by
    funext y
    exact fderiv_const_add c
  rw [heq]
  simpa [A, r, g₂r, Function.comp_def, smul_smul, ← mul_assoc,
    Complex.I_mul_I] using hc

/-- End-to-end differential bridge: a locally parametrized zero set with the
computed normalized two-jet has real angle Hessian `Eᵀ Q E`, where
`E v = (L v, -ℓ (L v))`.

All occurrences of Hessians in the conclusion are actual iterated real Fréchet
derivatives. Existence of the branch and the Schur-complement jet of the original
determinant remain explicit hypotheses; they are not silently assumed proven. -/
theorem real_angle_hessian_of_implicit_two_jet
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
    {ψ : X × ℂ → ℂ} {ψ₁ : X × ℂ → (X × ℂ) →L[ℂ] ℂ}
    {ψ₂ : (X × ℂ) →L[ℂ] (X × ℂ) →L[ℂ] ℂ}
    {g : X → ℂ} {g₁ : X → X →L[ℂ] ℂ}
    {g₂ : X →L[ℂ] X →L[ℂ] ℂ}
    (ℓ : X →L[ℂ] ℂ) (Q : (X × ℂ) →L[ℂ] (X × ℂ) →L[ℂ] ℂ)
    {d : ℂ} (hd : d ≠ 0)
    (hψ : ∀ᶠ y in 𝓝 (0, g 0), HasFDerivAt ψ (ψ₁ y) y)
    (hψ₂ : HasFDerivAt ψ₁ ψ₂ (0, g 0))
    (hg : ∀ᶠ y in 𝓝 (0 : X), HasFDerivAt g (g₁ y) y)
    (hg₂ : HasFDerivAt g₁ g₂ 0)
    (hzero : (fun y => ψ (y, g y)) =ᶠ[𝓝 (0 : X)] fun _ => 0)
    (hfirst : ∀ z, ψ₁ (0, g 0) z = -(ℓ z.1 + z.2) / d)
    (hsecond : ∀ z t, ψ₂ z t = -Q z t / d)
    (L : Y →L[ℝ] X) (a : ℂ) (v w : Y) :
    fderiv ℝ (fderiv ℝ (fun y => a + g (Complex.I • L y))) 0 v w =
      Q (L v, -ℓ (L v)) (L w, -ℓ (L w)) := by
  have h := implicit_hessian_of_normalized_two_jet ℓ Q hd hψ hψ₂ hg hg₂
    hzero hfirst hsecond (L v) (L w)
  rw [second_fderiv_eq hg hg₂] at h
  rw [second_real_angle hg hg₂ L a v w, h, neg_neg]

end Angle

section AffineBranch

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The explicit branch of an equation affine in its last variable is analytic.
This is the analytic-existence step in §3.5, conditional only on analyticity of
the coefficient functions and nonvanishing of the last-coordinate coefficient. -/
theorem analyticAt_affine_branch {K₀ K₁ : X → 𝕜} {x : X}
    (h₀ : AnalyticAt 𝕜 K₀ x) (h₁ : AnalyticAt 𝕜 K₁ x) (hn : K₁ x ≠ 0) :
    AnalyticAt 𝕜 (fun y => -K₀ y / K₁ y) x :=
  h₀.neg.div h₁ hn

omit [NormedSpace 𝕜 X] in
/-- On a neighbourhood, the quotient branch is exactly the unique root. -/
theorem affine_branch_local_unique {K₀ K₁ : X → 𝕜} {x : X}
    (h₁ : ContinuousAt K₁ x) (hn : K₁ x ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∀ z : 𝕜, K₀ y + z * K₁ y = 0 ↔ z = -K₀ y / K₁ y := by
  filter_upwards [h₁.eventually_ne hn] with y hy z
  constructor
  · intro hz
    apply (eq_div_iff hy).2
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hz)
  · intro hz
    rw [hz, div_mul_cancel₀ _ hy]
    simp

end AffineBranch

end Tournament.HessianDerivatives
