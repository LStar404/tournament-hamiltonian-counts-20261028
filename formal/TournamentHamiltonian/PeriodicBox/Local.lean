module

public import TournamentHamiltonian.PeriodicBox.Cosine

@[expose] public section

set_option autoImplicit false
namespace PeriodicBox
noncomputable section
open MeasureTheory Set Function TorusCluster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- Coordinates in S are on the actual short circle arc about a fixed center. -/
def arcEvent (S : Finset (Fin n)) (c r : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i ∈ S, circleDist (x i) c ≤ r}

/-- The real-coordinate counterpart of the arc event. -/
def realArc (S : Finset (Fin n)) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i ∈ S, |x i| ≤ r}

/-- Selected coordinates are integrated over the actual short real interval;
all other coordinates retain their length-π Lebesgue cell. -/
def mixedMeasure (S : Finset (Fin n)) (r : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => if i ∈ S then volume.restrict (Icc (-r) r)
    else cellMeasure (-Real.pi/2))

instance (S : Finset (Fin n)) (r : ℝ) : IsFiniteMeasure (mixedMeasure S r) := by
  unfold mixedMeasure
  have hi (i : Fin n) : IsFiniteMeasure
      (if i ∈ S then volume.restrict (Icc (-r) r) else cellMeasure (-Real.pi/2)) := by
    split_ifs <;> infer_instance
  infer_instance

lemma measurable_circle_coord (i : Fin n) (c : ℝ) :
    Measurable (fun x : Fin n → ℝ => circleDist (x i) c) := by
  unfold circleDist
  exact ((AddCircle.continuous_mk' Real.pi).comp
    ((continuous_apply i).sub continuous_const)).norm.measurable

lemma measurableSet_arcEvent (S : Finset (Fin n)) (c r : ℝ) :
    MeasurableSet (arcEvent S c r) := by
  unfold arcEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (measurable_circle_coord i c) measurable_const

lemma measurableSet_realArc (S : Finset (Fin n)) (r : ℝ) :
    MeasurableSet (realArc S r) := by
  unfold realArc
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((continuous_apply i : Continuous (fun x : Fin n → ℝ => x i)).abs.measurable) measurable_const

lemma arcEvent_periodic (S : Finset (Fin n)) (c r : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Function.update x j (x j+Real.pi) ∈ arcEvent S c r ↔ x ∈ arcEvent S c r := by
  apply forall_congr'
  intro i
  by_cases hi : i=j
  · subst i; simp [Function.update_self, circleDist_add_pi_left]
  · simp [Function.update_of_ne hi]

lemma arcEvent_shift_center (S : Finset (Fin n)) (c r : ℝ) (x : Fin n → ℝ) :
    (fun i => x i+c) ∈ arcEvent S c r ↔ x ∈ arcEvent S 0 r := by
  have hd (i : Fin n) : circleDist (x i+c) c = circleDist (x i) 0 := by
    simpa using circleDist_joint (x i) 0 c
  simp only [arcEvent, mem_ofPred_eq, hd]

lemma arcEvent_eq_realArc_on_cell (S : Finset (Fin n)) (r : ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ Real.pi/2) :
    x ∈ arcEvent S 0 r ↔ x ∈ realArc S r := by
  have hd (i : Fin n) : circleDist (x i) 0 = |x i| := by
    apply circleDist_eq_abs (by simpa using hx i) |>.trans
    simp
  simp only [arcEvent, realArc, mem_ofPred_eq, hd]

lemma mixedMeasure_eq_restrict (S : Finset (Fin n)) {r : ℝ}
    (hr : r ≤ Real.pi/2) :
    (boxMeasure n (-Real.pi/2)).restrict (realArc S r) = mixedMeasure S r := by
  have hset : realArc S r = Set.univ.pi (fun i => if i ∈ S then Icc (-r) r else univ) := by
    ext x
    simp only [realArc, mem_ofPred_eq, mem_univ_pi]
    constructor
    · intro h i
      split_ifs with hi
      · exact abs_le.mp (h i hi)
      · trivial
    · intro h i hi
      simpa only [ite_eq_left hi, mem_Icc, ← abs_le] using h i
  rw [hset, boxMeasure, Measure.restrict_pi_pi]
  unfold mixedMeasure
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, cellMeasure, restrict_Ioc_eq_restrict_Icc]
    apply Measure.restrict_restrict_of_subset
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · simp [hi]

/-- A short-circle-arc integral is exactly an integral over ordinary short real intervals.
The center c is fixed independently of x. This is a proved periodic box transport,
not an assumed measure-preserving nearest-representative map. -/
theorem unwrap_arc_integral (S : Finset (Fin n)) (c : ℝ) {r : ℝ}
    (hr : r ≤ Real.pi/2) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) (hp : CoordPeriodic f) :
    (∫ x, (arcEvent S c r).indicator f x ∂boxMeasure n (-Real.pi/2)) =
      ∫ x, f (fun i => x i+c) ∂mixedMeasure S r := by
  let g := (arcEvent S c r).indicator f
  have hM : 0 ≤ M := (abs_nonneg (f (fun _ => 0))).trans (hb _)
  have hg : Measurable g := hf.indicator (measurableSet_arcEvent S c r)
  have hgb (x : Fin n → ℝ) : |g x| ≤ M := by
    by_cases hx : x ∈ arcEvent S c r
    · simpa [g, hx] using hb x
    · simpa [g, hx] using hM
  have hgp : CoordPeriodic g := by
    intro x i
    simp only [g, Set.indicator_apply, arcEvent_periodic, hp x i]
  calc
    _ = ∫ x, g (fun i => x i+c) ∂boxMeasure n (-Real.pi/2) :=
      (integral_shift _ g hg hgb hgp (fun _ => c)).symm
    _ = ∫ x, (realArc S r).indicator (fun x => f (fun i => x i+c)) x
        ∂boxMeasure n (-Real.pi/2) := by
      apply integral_congr_ae
      rw [boxMeasure_eq_closed]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))]
        with x hx
      have hx' (i : Fin n) : |x i| ≤ Real.pi/2 := by
        have h := hx i (mem_univ i)
        apply abs_le.mpr
        constructor <;> linarith [h.1,h.2]
      simp only [g, Set.indicator_apply, arcEvent_shift_center,
        arcEvent_eq_realArc_on_cell S r x hx']
    _ = _ := by rw [integral_indicator (measurableSet_realArc S r), mixedMeasure_eq_restrict S hr]

/-- All local coordinates lie in the genuine real cube [-r,r]^n. -/
lemma mixedMeasure_univ (r : ℝ) :
    mixedMeasure (Finset.univ : Finset (Fin n)) r =
      (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi (fun _ => Icc (-r) r)) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  simp [mixedMeasure]

/-- Actual kernel/bad-event transport, including arbitrary finite chosen near-vertex sets. -/
theorem unwrap_badKernel (H : SimpleGraph (Fin n)) (root : Fin n) (t c : ℝ)
    (S : Finset (Fin n)) {r : ℝ} (hr : r ≤ Real.pi/2) :
    (∫ x, (arcEvent S c r).indicator (badKernel H root t) x
      ∂boxMeasure n (-Real.pi/2)) = ∫ x, badKernel H root t x ∂mixedMeasure S r := by
  rw [unwrap_arc_integral S c hr _ (measurable_badKernel H root t)
    (badKernel_abs_le_one H root t) (badKernel_periodic H root t)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => badKernel_joint H root t x c)

/-- Root differences in a single coherently unwrapped real cube. -/
def differenceBad (root : Fin n) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ i, t < |x i-x root|}

lemma rootBad_eq_differenceBad_on_cube (root : Fin n) (t : ℝ) {r : ℝ}
    (hr : 2*r ≤ Real.pi/2) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ r) :
    x ∈ rootBad root t ↔ x ∈ differenceBad root t := by
  have hd (i : Fin n) : circleDist (x i) (x root) = |x i-x root| := by
    apply circleDist_eq_abs
    calc
      |x i-x root| ≤ |x i|+|x root| := abs_sub _ _
      _ ≤ 2*r := by linarith [hx i, hx root]
      _ ≤ Real.pi/2 := hr
  simp only [rootBad, differenceBad, mem_ofPred_eq, hd]

/-- Exact all-local identity before the root-Gaussian domination step. Both the
cosine product and the bad event now use honest real differences on [-r,r]^n. -/
theorem unwrap_local_badKernel (H : SimpleGraph (Fin n)) (root : Fin n)
    (t c : ℝ) {r : ℝ} (hr : 2*r ≤ Real.pi/2) :
    (∫ x, (arcEvent Finset.univ c r).indicator (badKernel H root t) x
      ∂boxMeasure n (-Real.pi/2)) =
      ∫ x in Set.univ.pi (fun _ : Fin n => Icc (-r) r),
        (differenceBad root t).indicator (kernel H) x := by
  rw [unwrap_badKernel H root t c Finset.univ (by linarith [Real.pi_pos]), mixedMeasure_univ]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] with x hx
  have hx' (i : Fin n) : |x i| ≤ r := abs_le.mpr (hx i (mem_univ i))
  simp only [badKernel, Set.indicator_apply, rootBad_eq_differenceBad_on_cube root t hr x hx']

/-- The fixed sixteen-center, radius 3π/16 instance used by the proof plan. -/
theorem unwrap_sixteen_local_badKernel (H : SimpleGraph (Fin n)) (root : Fin n)
    (t : ℝ) (j : Fin 16) :
    (∫ x, (arcEvent Finset.univ (center j) (3*Real.pi/16)).indicator
      (badKernel H root t) x ∂boxMeasure n (-Real.pi/2)) =
      ∫ x in Set.univ.pi (fun _ : Fin n => Icc (-(3*Real.pi/16)) (3*Real.pi/16)),
        (differenceBad root t).indicator (kernel H) x :=
  unwrap_local_badKernel H root t (center j) (by linarith [Real.pi_pos])

/-- The integration event uses exactly the arc sets from the geometry unit. -/
lemma arcEvent_iff_subset_arc (S : Finset (Fin n)) (c r : ℝ) (x : Fin n → ℝ) :
    x ∈ arcEvent S c r ↔ S ⊆ TorusCluster.arc x c r := by
  simp only [arcEvent, mem_ofPred_eq, Finset.subset_iff, TorusCluster.mem_arc]

/-- Thus the all-local event is precisely A's empty-outlier case. -/
lemma arcEvent_univ_iff_no_outliers (c : ℝ) (x : Fin n → ℝ) :
    x ∈ arcEvent Finset.univ c (3*Real.pi/16) ↔ TorusCluster.outliers x c = ∅ := by
  rw [arcEvent_iff_subset_arc]
  simp [TorusCluster.outliers, TorusCluster.outer, Finset.univ_subset_iff]

end
end PeriodicBox
