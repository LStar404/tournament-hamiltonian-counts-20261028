module

public import TournamentHamiltonian.PeriodicBox.Basic
public import TournamentHamiltonian.TorusCluster.Product
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

set_option autoImplicit false
namespace PeriodicBox
noncomputable section
open MeasureTheory Set Function TorusCluster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

lemma circleDist_joint (x y c : ℝ) : circleDist (x+c) (y+c) = circleDist x y := by
  unfold circleDist
  congr 2
  ring

lemma circleDist_add_pi_left (x y : ℝ) :
    circleDist (x+Real.pi) y = circleDist x y := by
  simp only [circleDist, AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period, add_zero]

lemma circleDist_add_pi_right (x y : ℝ) :
    circleDist x (y+Real.pi) = circleDist x y := by
  rw [circleDist_symm, circleDist_add_pi_left, circleDist_symm]

lemma continuous_circleDist : Continuous (fun p : ℝ × ℝ => circleDist p.1 p.2) := by
  unfold circleDist
  exact (AddCircle.continuous_mk' Real.pi |>.comp (continuous_fst.sub continuous_snd)).norm

lemma continuous_edgeFactor (e : Sym2 (Fin m)) :
    Continuous (fun x : Fin m → ℝ => edgeFactor x e) := by
  induction e using Sym2.ind with
  | _ i j => simpa only [edgeFactor_mk, Function.comp_def, Pi.sub_apply] using
      (Real.continuous_cos.comp
        ((continuous_apply i).sub (continuous_apply j) :
          Continuous (fun x : Fin m → ℝ => x i-x j))).abs

lemma continuous_kernel (H : SimpleGraph (Fin m)) : Continuous (kernel H) := by
  unfold kernel
  exact continuous_finsetProd _ (fun e _ => continuous_edgeFactor e)

lemma kernel_nonneg (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) : 0 ≤ kernel H x := by
  exact Finset.prod_nonneg (fun e _ => edgeFactor_nonneg x e)

lemma kernel_le_one (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) : kernel H x ≤ 1 := by
  exact Finset.prod_le_one₀ (fun e _ => edgeFactor_nonneg x e) (fun e _ => edgeFactor_le_one x e)

lemma kernel_abs_le_one (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) : |kernel H x| ≤ 1 := by
  rw [abs_of_nonneg (kernel_nonneg H x)]
  exact kernel_le_one H x

lemma edgeFactor_periodic (x : Fin m → ℝ) (i : Fin m) (e : Sym2 (Fin m)) :
    edgeFactor (Function.update x i (x i+Real.pi)) e = edgeFactor x e := by
  induction e using Sym2.ind with
  | _ j k =>
    simp only [edgeFactor_mk]
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k; simp
    · subst j
      simp only [Function.update_self, Function.update_of_ne hk]
      rw [show x i+Real.pi-x k = (x i-x k)+Real.pi by ring, Real.cos_add_pi, abs_neg]
    · subst k
      simp only [Function.update_self, Function.update_of_ne hj]
      rw [show x j-(x i+Real.pi) = (x j-x i)-Real.pi by ring, Real.cos_sub_pi, abs_neg]
    · simp [Function.update_of_ne hj, Function.update_of_ne hk]

lemma kernel_periodic (H : SimpleGraph (Fin m)) : CoordPeriodic (kernel H) := by
  intro x i
  unfold kernel
  exact Finset.prod_congr rfl (fun e _ => edgeFactor_periodic x i e)

lemma kernel_joint (H : SimpleGraph (Fin m)) : JointInvariant (kernel H) := by
  intro x c
  unfold kernel
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ i j => simp only [edgeFactor_mk]; congr 2; ring

/-- The genuine circle-root bad event. Existential form is exactly max distance > t. -/
def rootBad (r : Fin m) (t : ℝ) : Set (Fin m → ℝ) :=
  {x | ∃ i, t < circleDist (x i) (x r)}

def badKernel (H : SimpleGraph (Fin m)) (r : Fin m) (t : ℝ) : (Fin m → ℝ) → ℝ :=
  (rootBad r t).indicator (kernel H)

lemma measurableSet_rootBad (r : Fin m) (t : ℝ) : MeasurableSet (rootBad r t) := by
  change MeasurableSet {x : Fin m → ℝ | ∃ i, t < circleDist (x i) (x r)}
  simp_rw [ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  have hc : Continuous (fun x : Fin m → ℝ => circleDist (x i) (x r)) := by
    unfold circleDist
    exact (AddCircle.continuous_mk' Real.pi |>.comp
      ((continuous_apply i).sub (continuous_apply r) :
        Continuous (fun x : Fin m → ℝ => x i-x r))).norm
  exact measurableSet_lt measurable_const hc.measurable

lemma measurable_badKernel (H : SimpleGraph (Fin m)) (r : Fin m) (t : ℝ) :
    Measurable (badKernel H r t) :=
  (continuous_kernel H).measurable.indicator (measurableSet_rootBad r t)

lemma badKernel_abs_le_one (H : SimpleGraph (Fin m)) (r : Fin m) (t : ℝ)
    (x : Fin m → ℝ) : |badKernel H r t x| ≤ 1 := by
  by_cases h : x ∈ rootBad r t
  · simpa [badKernel, h] using kernel_abs_le_one H x
  · simp [badKernel, h]

lemma rootBad_joint (r : Fin m) (t c : ℝ) (x : Fin m → ℝ) :
    (fun i => x i+c) ∈ rootBad r t ↔ x ∈ rootBad r t := by
  simp only [rootBad, mem_ofPred_eq, circleDist_joint]

lemma rootBad_periodic (r : Fin m) (t : ℝ) (x : Fin m → ℝ) (i : Fin m) :
    Function.update x i (x i+Real.pi) ∈ rootBad r t ↔ x ∈ rootBad r t := by
  apply exists_congr
  intro j
  by_cases hj : j=i <;> by_cases hr : r=i
  · subst j; subst r; simp [circleDist, Function.update_self]
  · subst j; simp [Function.update_self, Function.update_of_ne hr, circleDist_add_pi_left]
  · subst r; simp [Function.update_self, Function.update_of_ne hj, circleDist_add_pi_right]
  · simp [Function.update_of_ne hj, Function.update_of_ne hr]

lemma badKernel_periodic (H : SimpleGraph (Fin m)) (r : Fin m) (t : ℝ) :
    CoordPeriodic (badKernel H r t) := by
  intro x i
  simp only [badKernel, Set.indicator_apply, rootBad_periodic, kernel_periodic H x i]

lemma badKernel_joint (H : SimpleGraph (Fin m)) (r : Fin m) (t : ℝ) :
    JointInvariant (badKernel H r t) := by
  intro x c
  simp only [badKernel, Set.indicator_apply, rootBad_joint, kernel_joint H x c]

/-- Full/root identity instantiated to the actual retained-edge cosine product and
actual circle-distance event; no measure or transport premise remains. -/
theorem cosine_gauge (H : SimpleGraph (Fin (n+1))) (a t : ℝ) :
    (∫ x, badKernel H 0 t x ∂boxMeasure (n+1) a) =
      Real.pi * ∫ z, badKernel H 0 t (Fin.cons 0 z) ∂boxMeasure n a :=
  gauge_root_zero a _ (measurable_badKernel H 0 t) (badKernel_abs_le_one H 0 t)
    (badKernel_periodic H 0 t) (badKernel_joint H 0 t)

/-- The actual finite maximum of circle distances from the chosen root. -/
def maxRootDistance (r : Fin (n+1)) (x : Fin (n+1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => circleDist (x i) (x r))

lemma rootBad_iff_max (r : Fin (n+1)) (t : ℝ) (x : Fin (n+1) → ℝ) :
    x ∈ rootBad r t ↔ t < maxRootDistance r x := by
  simp [rootBad, maxRootDistance, Finset.lt_sup'_iff]

/-- The fixed-root real bad event on n nonroot coordinates. -/
def realBad (t : ℝ) : Set (Fin n → ℝ) := {z | ∃ i, t < |z i|}

lemma rootBad_cons_zero {t : ℝ} (ht : 0 ≤ t) (z : Fin n → ℝ)
    (hz : ∀ i, |z i| ≤ Real.pi/2) :
    Fin.cons 0 z ∈ rootBad 0 t ↔ z ∈ realBad t := by
  have hd (i : Fin n) : circleDist (z i) 0 = |z i| := by
    simpa only [sub_zero] using circleDist_eq_abs (x := z i) (y := 0) (by simpa using hz i)
  simp only [rootBad, realBad, mem_ofPred_eq, Fin.exists_fin_succ, Fin.cons_zero,
    Fin.cons_succ, hd]
  simp [circleDist, not_lt_of_ge ht]

/-- Exact Gauge on the closed centered real box, including the root bad event
written with genuine absolute real coordinates. Boundary faces are removed by
proved equality of restricted Lebesgue measures. -/
theorem cosine_gauge_real (H : SimpleGraph (Fin (n+1))) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, badKernel H 0 t x ∂boxMeasure (n+1) (-Real.pi/2)) =
      Real.pi * ∫ z, (realBad t).indicator (fun z => kernel H (Fin.cons 0 z)) z
        ∂boxMeasure n (-Real.pi/2) := by
  rw [cosine_gauge]
  congr 1
  apply integral_congr_ae
  rw [boxMeasure_eq_closed]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] with z hz
  have hz' (i : Fin n) : |z i| ≤ Real.pi/2 := by
    have hh := hz i (mem_univ i)
    apply abs_le.mpr
    constructor <;> linarith [hh.1, hh.2]
  simp only [badKernel, Set.indicator_apply, rootBad_cons_zero ht z hz']

/-- Every one of the sixteen centers is fixed before integration. No configuration-
dependent rotation or unproved representative map occurs in this identity. -/
theorem cosine_fixed_center_shift (H : SimpleGraph (Fin m)) (r : Fin m)
    (t a : ℝ) (j : Fin 16) :
    (∫ x, badKernel H r t (fun i => x i + center j) ∂boxMeasure m a) =
      ∫ x, badKernel H r t x ∂boxMeasure m a :=
  integral_shift a _ (measurable_badKernel H r t) (badKernel_abs_le_one H r t)
    (badKernel_periodic H r t) (fun _ => center j)

/-- The final Gauge API, stated entirely as ordinary Lebesgue set integrals over
closed centered boxes and with the actual finite maximum of circle distances. -/
theorem cosine_gauge_closed_volume (H : SimpleGraph (Fin (n+1))) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Set.univ.pi (fun _ : Fin (n+1) => Icc (-Real.pi/2) (Real.pi/2)),
      ({x | t < maxRootDistance 0 x} : Set (Fin (n+1) → ℝ)).indicator (kernel H) x) =
      Real.pi * ∫ z in Set.univ.pi (fun _ : Fin n => Icc (-Real.pi/2) (Real.pi/2)),
        (realBad t).indicator (fun z => kernel H (Fin.cons 0 z)) z := by
  have he : ({x | t < maxRootDistance 0 x} : Set (Fin (n+1) → ℝ)) = rootBad 0 t := by
    ext x
    exact (rootBad_iff_max 0 t x).symm
  rw [he]
  have hg := cosine_gauge_real H ht
  simpa only [boxMeasure_eq_closed, show -Real.pi/2+Real.pi = Real.pi/2 by ring,
    badKernel] using hg

/-- Moving a full π-box to any one of the sixteen fixed centers preserves the
actual integral. -/
theorem cosine_fixed_center_boxes (H : SimpleGraph (Fin m)) (r : Fin m)
    (t : ℝ) (j : Fin 16) :
    (∫ x, badKernel H r t x ∂boxMeasure m (-Real.pi/2)) =
      ∫ x, badKernel H r t x ∂boxMeasure m (center j-Real.pi/2) :=
  integral_boxes_eq _ _ _ (measurable_badKernel H r t) (badKernel_abs_le_one H r t)
    (badKernel_periodic H r t)

end
end PeriodicBox
