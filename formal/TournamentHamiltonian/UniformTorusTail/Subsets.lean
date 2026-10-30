module

public import TournamentHamiltonian.UniformTorusTail.Local

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

def selectedCoords (S : Finset (Fin m)) (x : Fin m → ℝ) : Fin S.card → ℝ :=
  fun k => x (S.equivFin.symm k).val

lemma selected_sum (S : Finset (Fin m)) (x : Fin m → ℝ) :
    (∑ k, selectedCoords S x k) = ∑ i ∈ S, x i := by
  rw [← Finset.sum_coe_sort S x]
  exact S.equivFin.symm.sum_comp (fun i : S => x i.val)

lemma selected_variance (S : Finset (Fin m)) (x : Fin m → ℝ) :
    varianceOn (selectedCoords S x) Finset.univ = varianceOn x S := by
  have hm : meanOn (selectedCoords S x) Finset.univ = meanOn x S := by
    simp only [meanOn, Finset.card_univ, Fintype.card_fin, selected_sum]
  simp only [varianceOn, hm]
  rw [← Finset.sum_coe_sort S (fun i => (x i-meanOn x S)^2)]
  exact S.equivFin.symm.sum_comp (fun i : S => (x i.val-meanOn x S)^2)

/-- Exact integration of a selected-coordinate function over the actual mixed
Lebesgue measure: every outlier contributes one factor π, and no sqrt(p) occurs. -/
theorem mixed_selected_integral (S : Finset (Fin m)) (r : ℝ)
    (g : (Fin S.card → ℝ) → ℝ) :
    (∫ x, g (selectedCoords S x) ∂mixedMeasure S r) =
      Real.pi^(m-S.card) * ∫ z, g z ∂cubeMeasure S.card (-r) r := by
  let : Fintype S := Subtype.fintype (fun i : Fin m => i ∈ S)
  let μ : Fin m → Measure ℝ := fun i =>
    if i ∈ S then volume.restrict (Icc (-r) r) else cellMeasure (-Real.pi/2)
  have hfinite (i : Fin m) : IsFiniteMeasure (μ i) := by
    dsimp [μ]; split_ifs <;> infer_instance
  let F : (S → ℝ) → ℝ := fun z => g (fun k => z (S.equivFin.symm k))
  have hs := (measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ S)).integral_comp'
    (fun y : (S → ℝ) × ({i : Fin m // i ∉ S} → ℝ) => F y.1)
  have hμS : (Measure.pi (fun i : S => μ i.val)) =
      Measure.pi (fun _ : S => volume.restrict (Icc (-r) r)) := by
    congr 1; funext i; simp [μ,i.property]
  have hμC : (Measure.pi (fun i : {i : Fin m // i ∉ S} => μ i.val)) =
      Measure.pi (fun _ : {i : Fin m // i ∉ S} => cellMeasure (-Real.pi/2)) := by
    congr 1; funext i; simp [μ,i.property]
  have hleft : (fun x : Fin m → ℝ =>
      (fun y : (S → ℝ) × ({i : Fin m // i ∉ S} → ℝ) => F y.1)
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => ℝ) (fun i => i ∈ S) x)) =
      fun x => g (selectedCoords S x) := by rfl
  rw [hleft] at hs
  change (∫ x, g (selectedCoords S x) ∂Measure.pi μ) =
    ∫ y : (S → ℝ) × ({i : Fin m // i ∉ S} → ℝ), F y.1
      ∂(Measure.pi (fun i : S => μ i.val)).prod
        (Measure.pi (fun i : {i : Fin m // i ∉ S} => μ i.val)) at hs
  rw [hμS, hμC, integral_fun_fst] at hs
  have hmass : (Measure.pi (fun _ : {i : Fin m // i ∉ S} => cellMeasure (-Real.pi/2))).real univ =
      Real.pi^(m-S.card) := by
    simp [measureReal_def, Measure.pi_univ, cellMeasure, Real.pi_pos.le,
      Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hmass, smul_eq_mul] at hs
  have hp := (measurePreserving_piCongrLeft
    (fun _ : Fin S.card => volume.restrict (Icc (-r) r)) S.equivFin).integral_comp' g
  have hv (z : S → ℝ) : (MeasurableEquiv.piCongrLeft
      (fun _ : Fin S.card => ℝ) S.equivFin) z = fun k => z (S.equivFin.symm k) := by
    ext k
    obtain ⟨j,rfl⟩ := S.equivFin.surjective k
    simp [MeasurableEquiv.coe_piCongrLeft]
  simp only [hv] at hp
  change (∫ z, F z ∂Measure.pi (fun _ : S => volume.restrict (Icc (-r) r))) =
    ∫ z, g z ∂cubeMeasure S.card (-r) r at hp
  rw [hp] at hs
  exact hs

end UniformTorusTail

namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The genuine centered complete-cluster Gaussian supplied by A's deleted-degree estimate. -/
def clusterDensity (p : ℕ) (x : Fin p → ℝ) : ℝ :=
  Real.exp (-((p : ℝ)-4)/2*varianceOn x Finset.univ)

lemma clusterDensity_nonneg (p : ℕ) (x : Fin p → ℝ) : 0 ≤ clusterDensity p x := (Real.exp_pos _).le

lemma clusterDensity_le_one (p : ℕ) (hp : 4 ≤ p) (x : Fin p → ℝ) : clusterDensity p x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hv : 0 ≤ varianceOn x Finset.univ := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hv

lemma clusterDensity_measurable (p : ℕ) : Measurable (clusterDensity p) := by
  unfold clusterDensity varianceOn meanOn
  fun_prop

lemma clusterDensity_succ (n : ℕ) (x : Fin (n+1) → ℝ) :
    clusterDensity (n+1) x = density n (1-4/((n+1 : ℕ) : ℝ)) (fun i => x i.succ-x 0) := by
  have he := anchorDensity_pair_energy n (1-4/((n+1 : ℕ) : ℝ)) (x 0) (Fin.tail x)
  simp only [anchorDensity, Fin.tail, Fin.cons_self_tail] at he
  rw [he, pairEnergy_eq_completeEnergy, completeEnergy_eq_variance]
  simp only [Finset.card_univ, Fintype.card_fin, clusterDensity, Nat.cast_add, Nat.cast_one]
  congr 1
  field_simp

/-- The short cluster keeps its exact root normalizer. There is no additional sqrt(p). -/
theorem cluster_cube_bound (p : ℕ) (hp : 8 ≤ p) :
    (∫ x, clusterDensity p x ∂cubeMeasure p (-localRadius) localRadius) ≤
      Real.pi * Real.exp 4 * Z p 1 := by
  cases p with
  | zero => omega
  | succ n =>
    let a : ℝ := 1-4/((n+1 : ℕ) : ℝ)
    have ha := perturbation_scale_pos (n+1) hp
    simp_rw [clusterDensity_succ]
    have h := cube_anchor_bound n (density n a) (density_integrable n a ha)
      (density_measurable n a) (density_nonneg n a) (-localRadius) localRadius
    have hlen : max (localRadius-(-localRadius)) 0 ≤ Real.pi := by
      apply max_le
      · dsimp [localRadius]; linarith [Real.pi_pos]
      · exact Real.pi_pos.le
    have h' := h.trans (mul_le_mul_of_nonneg_right hlen (partition_pos n a ha).le)
    have hz := perturbation_normalization_loss (n+1) hp
    simp only [Z, Nat.add_sub_cancel] at hz
    have hh := mul_le_mul_of_nonneg_left hz Real.pi_pos.le
    exact h'.trans (by simpa [Z, mul_assoc, partition, a] using hh)

lemma continuous_insideProduct {m : ℕ} (H : SimpleGraph (Fin m)) (S : Finset (Fin m)) :
    Continuous (fun x => insideProduct H x S) := by
  exact continuous_finsetProd _ (fun e _ => continuous_edgeFactor e)

lemma insideProduct_le_one {m : ℕ} (H : SimpleGraph (Fin m)) (S : Finset (Fin m)) (x : Fin m → ℝ) :
    insideProduct H x S ≤ 1 :=
  Finset.prod_le_one₀ (fun e _ => edgeFactor_nonneg x e) (fun e _ => edgeFactor_le_one x e)

lemma insideProduct_abs_le_one {m : ℕ} (H : SimpleGraph (Fin m)) (S : Finset (Fin m)) (x : Fin m → ℝ) :
    |insideProduct H x S| ≤ 1 := by
  rw [abs_of_nonneg (insideProduct_nonneg H x S)]
  exact insideProduct_le_one H S x

lemma insideProduct_periodic {m : ℕ} (H : SimpleGraph (Fin m)) (S : Finset (Fin m)) :
    CoordPeriodic (fun x => insideProduct H x S) := by
  intro x i
  exact Finset.prod_congr rfl (fun e _ => edgeFactor_periodic x i e)

lemma insideProduct_joint {m : ℕ} (H : SimpleGraph (Fin m)) (S : Finset (Fin m)) :
    JointInvariant (fun x => insideProduct H x S) := by
  intro x c
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ i j => simp only [edgeFactor_mk]; congr 2; ring

/-- Actual arbitrary-subset cluster integration, the main outlier normalization bridge. -/
theorem inside_cluster_integral_bound {m : ℕ} (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (S : Finset (Fin m)) (hS : 8 ≤ S.card) (c : ℝ) :
    (∫ x, (arcEvent S c localRadius).indicator (fun x => insideProduct H x S) x
      ∂boxMeasure m (-Real.pi/2)) ≤
      Real.pi^(m-S.card) * (Real.pi*Real.exp 4*Z S.card 1) := by
  rw [unwrap_arc_integral S c (by dsimp [localRadius]; linarith [Real.pi_pos]) _
    (continuous_insideProduct H S).measurable (insideProduct_abs_le_one H S) (insideProduct_periodic H S)]
  have hj (x : Fin m → ℝ) : insideProduct H (fun i => x i+c) S = insideProduct H x S :=
    insideProduct_joint H S x c
  simp_rw [hj]
  have hi := integrable_bounded (mixedMeasure S localRadius)
    (continuous_insideProduct H S).measurable (insideProduct_abs_le_one H S)
  have hgm : Measurable (fun x : Fin m → ℝ => clusterDensity S.card (selectedCoords S x)) :=
    (clusterDensity_measurable S.card).comp (by unfold selectedCoords; fun_prop)
  have hgb (x : Fin m → ℝ) : |clusterDensity S.card (selectedCoords S x)| ≤ 1 := by
    rw [abs_of_nonneg (clusterDensity_nonneg _ _)]
    exact clusterDensity_le_one _ (by omega) _
  have hgi := integrable_bounded (mixedMeasure S localRadius) hgm hgb
  have hp : ∀ᵐ x ∂mixedMeasure S localRadius,
      insideProduct H x S ≤ clusterDensity S.card (selectedCoords S x) := by
    rw [← mixedMeasure_eq_restrict S (by dsimp [localRadius]; linarith [Real.pi_pos])]
    filter_upwards [ae_restrict_mem (measurableSet_realArc S localRadius)] with x hx
    have hspan (i : Fin m) (hi : i∈S) (j : Fin m) (hj : j∈S) : |x i-x j| ≤ Real.pi/2 := by
      have hi' := hx i hi
      have hj' := hx j hj
      have hab := abs_sub (x i) (x j)
      dsimp [localRadius] at hi' hj'
      linarith [Real.pi_pos]
    simpa only [clusterDensity, selected_variance] using inside_gaussian_bound H hdegree x S hspan
  have h := integral_mono_ae hi hgi hp
  rw [mixed_selected_integral] at h
  exact h.trans (mul_le_mul_of_nonneg_left (cluster_cube_bound S.card hS) (by positivity))

end UniformTorusTail
