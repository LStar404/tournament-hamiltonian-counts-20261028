module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

public section

/-!
# The actual determinant and its local last-coordinate branch

This file concerns the manuscript's genuine determinant
`K(y) = det (I - M diagonal(y))`, where `M = A + I/2` in §3.
It proves affine dependence on any selected coordinate and the analyticity and
local uniqueness of the explicit branch. The nonzero-coefficient hypothesis is
left explicit: proving it from regular-tournament structure is a separate step.
-/

open Filter
open scoped Topology Matrix

namespace Tournament.HessianBranch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant from the original implicit equation, for a general fixed matrix. -/
@[expose] def K (M : Matrix n n ℂ) (y : n → ℂ) : ℂ :=
  (1 - M * Matrix.diagonal y).det

/-- Constant coefficient after selecting coordinate `j` for elimination. -/
@[expose] def K₀ (M : Matrix n n ℂ) (j : n) (y : n → ℂ) : ℂ :=
  K M (Function.update y j 0)

/-- Linear coefficient, expressed by replacing the selected column by `-M[:,j]`. -/
@[expose] def K₁ (M : Matrix n n ℂ) (j : n) (y : n → ℂ) : ℂ :=
  ((1 - M * Matrix.diagonal (Function.update y j 0)).updateCol j
    (fun i => -M i j)).det

/-- The determinant is affine, not merely differentiable, in the eliminated coordinate. -/
theorem K_update_affine (M : Matrix n n ℂ) (j : n) (y : n → ℂ) (z : ℂ) :
    K M (Function.update y j z) = K₀ M j y + z * K₁ M j y := by
  let B := (1 : Matrix n n ℂ) - M * Matrix.diagonal (Function.update y j 0)
  let e : n → ℂ := fun i => (1 : Matrix n n ℂ) i j
  let a : n → ℂ := fun i => -M i j
  have hmat : (1 : Matrix n n ℂ) - M * Matrix.diagonal (Function.update y j z) =
      B.updateCol j (e + z • a) := by
    ext i k
    by_cases hk : k = j
    · subst k
      simp [B, e, a, Matrix.mul_diagonal, Matrix.sub_apply, mul_comm, sub_eq_add_neg]
    · simp [B, Matrix.updateCol_ne hk, Matrix.mul_diagonal, Matrix.sub_apply,
        Function.update_of_ne hk]
  have he : B.updateCol j e = B := by
    ext i k
    by_cases hk : k = j
    · subst k
      simp [B, e, Matrix.mul_diagonal, Matrix.sub_apply]
    · simp [Matrix.updateCol_ne hk]
  unfold K
  rw [hmat, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, he]
  rfl

/-- The paper's difference formula for the linear coefficient. -/
theorem K₁_eq_difference (M : Matrix n n ℂ) (j : n) (y : n → ℂ) :
    K₁ M j y = K M (Function.update y j 1) - K M (Function.update y j 0) := by
  rw [K_update_affine, one_mul]
  change K₁ M j y = K₀ M j y + K₁ M j y - K₀ M j y
  ring

/-- The coefficient is the actual complex derivative in the selected coordinate. -/
theorem hasDerivAt_K_update (M : Matrix n n ℂ) (j : n) (y : n → ℂ) (z : ℂ) :
    HasDerivAt (fun t => K M (Function.update y j t)) (K₁ M j y) z := by
  have h := (hasDerivAt_const z (K₀ M j y)).add
    ((hasDerivAt_id z).mul_const (K₁ M j y))
  convert! h using 1 <;> simp [K_update_affine]
  rfl

omit [DecidableEq n] in
private theorem analyticAt_coordinate (i : n) (y : n → ℂ) :
    AnalyticAt ℂ (fun x : n → ℂ => x i) y := by
  convert! (ContinuousLinearMap.proj i : (n → ℂ) →L[ℂ] ℂ).analyticAt y using 1

/-- Every coordinate of the determinant is a polynomial, hence analytic. -/
theorem analyticAt_K (M : Matrix n n ℂ) (y : n → ℂ) : AnalyticAt ℂ (K M) y := by
  unfold K
  simp_rw [Matrix.det_apply', Matrix.sub_apply, Matrix.mul_diagonal]
  apply Finset.analyticAt_fun_sum
  intro σ hσ
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact analyticAt_const.sub
    (analyticAt_const.mul (analyticAt_coordinate i y))

/-- Overwriting one coordinate by a fixed scalar is an analytic map. -/
theorem analyticAt_update (j : n) (z : ℂ) (y : n → ℂ) :
    AnalyticAt ℂ (fun x : n → ℂ => Function.update x j z) y := by
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = j
  · subst i
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : n → ℂ => z) y)
  · simpa [Function.update_of_ne hi] using
      analyticAt_coordinate i y

theorem analyticAt_K₀ (M : Matrix n n ℂ) (j : n) (y : n → ℂ) :
    AnalyticAt ℂ (K₀ M j) y :=
  (analyticAt_K M _).comp (analyticAt_update j 0 y)

theorem analyticAt_K₁ (M : Matrix n n ℂ) (j : n) (y : n → ℂ) :
    AnalyticAt ℂ (K₁ M j) y := by
  have h := ((analyticAt_K M _).comp (analyticAt_update j 1 y)).sub
    ((analyticAt_K M _).comp (analyticAt_update j 0 y))
  change AnalyticAt ℂ (fun x => K M (Function.update x j 1) -
    K M (Function.update x j 0)) y at h
  simpa only [← K₁_eq_difference] using h

/-- Explicit last-coordinate branch for the original determinant. -/
@[expose] noncomputable def branch (M : Matrix n n ℂ) (j : n) (y : n → ℂ) : ℂ :=
  -K₀ M j y / K₁ M j y

theorem analyticAt_branch (M : Matrix n n ℂ) (j : n) (y : n → ℂ)
    (hn : K₁ M j y ≠ 0) : AnalyticAt ℂ (branch M j) y :=
  (analyticAt_K₀ M j y).neg.div (analyticAt_K₁ M j y) hn

/-- Locally, solving the genuine determinant equation is equivalent to the explicit quotient. -/
theorem branch_local_unique (M : Matrix n n ℂ) (j : n) (y : n → ℂ)
    (hn : K₁ M j y ≠ 0) :
    ∀ᶠ x in 𝓝 y, ∀ z : ℂ, K M (Function.update x j z) = 0 ↔ z = branch M j x := by
  filter_upwards [(analyticAt_K₁ M j y).continuousAt.eventually_ne hn] with x hx z
  rw [K_update_affine]
  unfold branch
  constructor
  · intro hz
    apply (eq_div_iff hx).2
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hz)
  · intro hz
    rw [hz, div_mul_cancel₀ _ hx]
    simp

/-- The explicit analytic branch passes through any basepoint on the determinant zero set. -/
theorem branch_at_base (M : Matrix n n ℂ) (j : n) (y : n → ℂ)
    (hn : K₁ M j y ≠ 0) (hK : K M y = 0) : branch M j y = y j := by
  have h := (branch_local_unique M j y hn).self_of_nhds (y j)
  apply Eq.symm
  apply h.mp
  simpa using hK

/-- Exponential coordinates used before passing to angle variables. -/
@[expose] noncomputable def expCoordinates (z : ℂ) (t : n → ℂ) : n → ℂ :=
  fun i => z * Complex.exp (t i)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem expCoordinates_zero (z : ℂ) : expCoordinates (n := n) z 0 = fun _ => z := by
  ext i
  simp [expCoordinates]

omit [DecidableEq n] in
theorem analyticAt_expCoordinates (z : ℂ) (t : n → ℂ) :
    AnalyticAt ℂ (expCoordinates z) t := by
  apply AnalyticAt.pi
  intro i
  exact analyticAt_const.mul (analyticAt_coordinate i t).cexp

/-- The normalized logarithmic branch used in §3.5. -/
@[expose] noncomputable def logBranch (M : Matrix n n ℂ) (j : n) (z : ℂ) (t : n → ℂ) : ℂ :=
  Complex.log (branch M j (expCoordinates z t) / z)

/-- Analyticity of the actual determinant's normalized logarithmic branch. -/
theorem analyticAt_logBranch (M : Matrix n n ℂ) (j : n) {z : ℂ}
    (hz : z ≠ 0) (hn : K₁ M j (fun _ => z) ≠ 0) (hK : K M (fun _ => z) = 0) :
    AnalyticAt ℂ (logBranch M j z) 0 := by
  have hb : branch M j (fun _ => z) = z := branch_at_base M j _ hn hK
  have ha : AnalyticAt ℂ (fun t => branch M j (expCoordinates z t) / z) 0 := by
    apply AnalyticAt.div_const
    exact (analyticAt_branch M j _ (by simpa using hn)).comp (analyticAt_expCoordinates z 0)
  apply ha.clog
  simp [hb, hz]

theorem logBranch_zero (M : Matrix n n ℂ) (j : n) {z : ℂ}
    (hz : z ≠ 0) (hn : K₁ M j (fun _ => z) ≠ 0) (hK : K M (fun _ => z) = 0) :
    logBranch M j z 0 = 0 := by
  have hb : branch M j (fun _ => z) = z := branch_at_base M j _ hn hK
  simp [logBranch, hb, hz]

/-- The logarithmic branch solves the original determinant equation locally.
No implicit equation is assumed here: it follows from the explicit determinant branch. -/
theorem logBranch_local_zero (M : Matrix n n ℂ) (j : n) {z : ℂ}
    (hz : z ≠ 0) (hn : K₁ M j (fun _ => z) ≠ 0) (hK : K M (fun _ => z) = 0) :
    ∀ᶠ t in 𝓝 (0 : n → ℂ),
      K M (Function.update (expCoordinates z t) j (z * Complex.exp (logBranch M j z t))) = 0 := by
  have hb : branch M j (fun _ => z) = z := branch_at_base M j _ hn hK
  have hc := (analyticAt_expCoordinates (n := n) z 0).continuousAt
  have huniq : ∀ᶠ t in 𝓝 (0 : n → ℂ), ∀ a : ℂ,
      K M (Function.update (expCoordinates z t) j a) = 0 ↔
        a = branch M j (expCoordinates z t) := by
    exact hc.eventually (by simpa using branch_local_unique M j (fun _ => z) hn)
  have hbc : ContinuousAt (fun t => branch M j (expCoordinates z t)) 0 :=
    ((analyticAt_branch M j _ (by simpa using hn)).comp
      (analyticAt_expCoordinates z 0)).continuousAt
  have hbn : branch M j (expCoordinates z (0 : n → ℂ)) ≠ 0 := by simpa [hb] using hz
  filter_upwards [huniq, hbc.eventually_ne hbn] with t ht hbt
  apply (ht _).mpr
  rw [logBranch, Complex.exp_log (div_ne_zero hbt hz)]
  field_simp

end Tournament.HessianBranch
