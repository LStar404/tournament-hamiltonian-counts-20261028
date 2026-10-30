module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace PeriodicBox
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal

/-- Ordinary Lebesgue measure on one period; its total mass is π, not 1. -/
def cellMeasure (a : ℝ) : Measure ℝ := volume.restrict (Ioc a (a + Real.pi))
instance (a : ℝ) : IsFiniteMeasure (cellMeasure a) := by
  dsimp [cellMeasure]; infer_instance

/-- Finite product of restricted ordinary Lebesgue measures. -/
def boxMeasure (n : ℕ) (a : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => cellMeasure a)
instance (n : ℕ) (a : ℝ) : IsFiniteMeasure (boxMeasure n a) := by
  dsimp [boxMeasure]; infer_instance

def CoordPeriodic {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x i, f (Function.update x i (x i + Real.pi)) = f x

def JointInvariant {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x c, f (fun i => x i + c) = f x

lemma integrable_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ x, |f x| ≤ M) : Integrable f μ :=
  (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma integral_cell (a : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂cellMeasure a) = ∫ x in a..a + Real.pi, f x := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rfl

@[simp] lemma cell_mass (a : ℝ) : (cellMeasure a).real univ = Real.pi := by
  simp [cellMeasure, measureReal_def, Real.pi_pos.le]

lemma integral_cons {n : ℕ} (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) :
    (∫ x, f x ∂boxMeasure (n+1) a) =
      ∫ y, ∫ z, f (Fin.cons y z) ∂boxMeasure n a ∂cellMeasure a := by
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => cellMeasure a) 0).symm
  have hc : Measurable (fun x : ℝ × (Fin n → ℝ) => f (Fin.cons x.1 x.2)) := by
    apply hf.comp
    fun_prop
  have hi := integrable_bounded ((cellMeasure a).prod (boxMeasure n a)) hc
    (fun x => hb (Fin.cons x.1 x.2))
  calc
    _ = ∫ x : ℝ × (Fin n → ℝ), f (Fin.cons x.1 x.2)
        ∂(cellMeasure a).prod (boxMeasure n a) := by
      simpa only [boxMeasure, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
        using (hmp.integral_comp' f).symm
    _ = _ := integral_prod _ hi

lemma periodic_fiber {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hp : CoordPeriodic f)
    (x : Fin n → ℝ) (i : Fin n) :
    Periodic (fun y => f (Function.update x i y)) Real.pi := by
  intro y
  simpa using hp (Function.update x i y) i

lemma periodic_cons {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hp : CoordPeriodic f) (y : ℝ) : CoordPeriodic (fun z => f (Fin.cons y z)) := by
  intro z i
  simpa only [Fin.cons_update, Fin.cons_succ] using hp (Fin.cons y z) i.succ

lemma integral_periodic_shift (a c : ℝ) {f : ℝ → ℝ} (hp : Periodic f Real.pi) :
    (∫ x, f (x+c) ∂cellMeasure a) = ∫ x, f x ∂cellMeasure a := by
  rw [integral_cell, intervalIntegral.integral_comp_add_right, integral_cell]
  rw [show a+Real.pi+c = (a+c)+Real.pi by ring]
  exact hp.intervalIntegral_add_eq (a+c) a

/-- Coordinatewise fixed translations preserve the integral of any bounded measurable
coordinatewise π-periodic function over an ordinary Lebesgue period box. -/
theorem integral_shift {n : ℕ} (a : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    (hp : CoordPeriodic f) (c : Fin n → ℝ) :
    (∫ x, f (fun i => x i + c i) ∂boxMeasure n a) = ∫ x, f x ∂boxMeasure n a := by
  induction n with
  | zero =>
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrArg f (Subsingleton.elim _ _))
  | succ n ih =>
      have hshift : Measurable (fun x : Fin (n+1) → ℝ => f (fun i => x i+c i)) :=
        hf.comp (by fun_prop)
      rw [integral_cons a (fun x => f (fun i => x i+c i)) hshift (fun x => hb _),
        integral_cons a f hf hb]
      have he (y : ℝ) :
          (∫ z, f (fun i => (Fin.cons y z : Fin (n+1) → ℝ) i + c i) ∂boxMeasure n a) =
          ∫ z, f (Fin.cons (y+c 0) z) ∂boxMeasure n a := by
        have hfn : (fun z : Fin n → ℝ => f (fun i => (Fin.cons y z : Fin (n+1) → ℝ) i + c i)) =
            fun z => f (Fin.cons (y+c 0) (fun i => z i + c i.succ)) := by
          funext z; congr 1; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
        rw [hfn]
        exact ih (fun z => f (Fin.cons (y+c 0) z)) (hf.comp (by fun_prop))
          (fun z => hb _) (periodic_cons hp _) (fun i => c i.succ)
      simp_rw [he]
      apply integral_periodic_shift a (c 0) (f := fun y => ∫ z, f (Fin.cons y z) ∂boxMeasure n a)
      intro y
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      simpa using hp (Fin.cons y z) 0


/-- The ordinary Lebesgue integral is independent of the location of the length-π box. -/
theorem integral_boxes_eq {n : ℕ} (a b : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M) (hp : CoordPeriodic f) :
    (∫ x, f x ∂boxMeasure n a) = ∫ x, f x ∂boxMeasure n b := by
  induction n with
  | zero =>
      have hm : boxMeasure 0 a = boxMeasure 0 b := by
        unfold boxMeasure
        congr 1
        funext i
        exact Fin.elim0 i
      rw [hm]
  | succ n ih =>
      rw [integral_cons a f hf hb, integral_cons b f hf hb]
      have he (y : ℝ) : (∫ z, f (Fin.cons y z) ∂boxMeasure n a) =
          ∫ z, f (Fin.cons y z) ∂boxMeasure n b :=
        ih (fun z => f (Fin.cons y z)) (hf.comp (by fun_prop))
          (fun z => hb _) (periodic_cons hp y)
      simp_rw [he]
      rw [integral_cell, integral_cell]
      apply Function.Periodic.intervalIntegral_add_eq
      intro y
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by simpa using hp (Fin.cons y z) 0)

/-- Exact full/root gauge identity with ordinary volume. The factor is π. -/
theorem gauge_root_zero {n : ℕ} (a : ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, |f x| ≤ M)
    (hp : CoordPeriodic f) (hj : JointInvariant f) :
    (∫ x, f x ∂boxMeasure (n+1) a) =
      Real.pi * ∫ z, f (Fin.cons 0 z) ∂boxMeasure n a := by
  rw [integral_cons a f hf hb]
  have he (y : ℝ) : (∫ z, f (Fin.cons y z) ∂boxMeasure n a) =
      ∫ z, f (Fin.cons 0 z) ∂boxMeasure n a := by
    calc
      _ = ∫ z, f (Fin.cons 0 (fun i => z i + (-y))) ∂boxMeasure n a := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro z
        symm
        have hvec : (fun i => (Fin.cons y z : Fin (n+1) → ℝ) i + (-y)) =
            Fin.cons 0 (fun i => z i+(-y)) := by
          ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
        simpa only [hvec] using hj (Fin.cons y z) (-y)
      _ = _ := integral_shift a (fun z => f (Fin.cons 0 z)) (hf.comp (by fun_prop))
        (fun z => hb _) (periodic_cons hp _) (fun _ => -y)
  simp_rw [he]
  simp [integral_const, cell_mass]

/-- The product measure is literally restricted ordinary volume on the half-open box. -/
lemma boxMeasure_eq_restrict (n : ℕ) (a : ℝ) :
    boxMeasure n a = (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi (fun _ => Ioc a (a+Real.pi))) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  rfl

/-- End faces have zero measure, so closed and half-open cells define the same measure. -/
lemma boxMeasure_eq_closed (n : ℕ) (a : ℝ) :
    boxMeasure n a = (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi (fun _ => Icc a (a+Real.pi))) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  simp only [boxMeasure, cellMeasure, restrict_Ioc_eq_restrict_Icc]

lemma boxMeasure_eq_left_closed (n : ℕ) (a : ℝ) :
    boxMeasure n a = (volume : Measure (Fin n → ℝ)).restrict
      (Set.univ.pi (fun _ => Ico a (a+Real.pi))) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  simp only [boxMeasure, cellMeasure, restrict_Ico_eq_restrict_Ioc]

/-- The factor π is audited by the exact volume of the full box. -/
@[simp] lemma box_mass (n : ℕ) (a : ℝ) : (boxMeasure n a).real univ = Real.pi^n := by
  simp [boxMeasure, measureReal_def, Measure.pi_univ, cellMeasure, Real.pi_pos.le]

lemma integral_one (n : ℕ) (a : ℝ) :
    (∫ _x : Fin n → ℝ, (1:ℝ) ∂boxMeasure n a) = Real.pi^n := by
  simp

/-- Relabeling is a genuine ordinary-volume integral identity, not a change-of-variables
assumption. This allows any chosen root labeling, including Fin.last. -/
theorem integral_reindex {n : ℕ} (a : ℝ) (e : Fin n ≃ Fin n)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f (fun i => x (e.symm i)) ∂boxMeasure n a) =
      ∫ x, f x ∂boxMeasure n a := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => cellMeasure a) e).integral_comp' f
  have he (x : Fin n → ℝ) : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e) x =
      (fun i => x (e.symm i)) := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [MeasurableEquiv.coe_piCongrLeft]
  simpa only [boxMeasure, he] using h

end
end PeriodicBox
