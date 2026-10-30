module

public import TournamentHamiltonian.UniformTorusTail.Limits

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A graph-independent explicit upper envelope. -/
def tailEnvelope (m : ℕ) (eps : ℝ) : ℝ :=
  farEnvelope m + outlierEnvelope m + localEnvelope m (window m eps)

lemma tendsto_tailEnvelope_zero (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun m => tailEnvelope m eps) atTop (𝓝 0) := by
  have h := (tendsto_farEnvelope_zero.add tendsto_outlierEnvelope_zero).add
    (tendsto_localEnvelope_window_zero eps heps)
  simpa only [zero_add, tailEnvelope] using h

lemma tailIntegral_nonneg {n : ℕ} (H : SimpleGraph (Fin (n+1))) (t : ℝ) : 0 ≤ tailIntegral H t :=
  integral_nonneg (fun z => Set.indicator_nonneg (fun z _ => kernel_nonneg H (Fin.cons 0 z)) z)

/-- Every graph is bounded by the same explicit real sequence. -/
theorem normalized_tailEnvelope_bound {n : ℕ} (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ n+1) (hb : beta (n+1) < 1) (eps : ℝ) :
    tailIntegral H (window (n+1) eps) / Z (n+1) 1 ≤ tailEnvelope (n+1) eps := by
  have ht : 0 ≤ window (n+1) eps := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h := normalized_tail_bound H hdegree hm hb (window (n+1) eps) ht
  simpa only [tailEnvelope, farEnvelope, outlierEnvelope, localEnvelope,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h

/-- Uniformity is explicit: the dimension threshold is chosen before H. No sequence
of graphs, forest regularity, or assumed torus estimate is required. -/
theorem uniform_deleted_torus_tail (eps : ℝ) (heps : 0 < eps) :
    ∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SimpleGraph (Fin (n+1)), (∀ i, H.degree i ≤ 2) →
        tailIntegral H (window (n+1) eps) ≤ eta * Z (n+1) 1 := by
  intro eta heta
  have he := ((tendsto_tailEnvelope_zero eps heps).comp (tendsto_add_atTop_nat 1)).eventually_lt_const heta
  have hb := (tendsto_beta_zero.comp (tendsto_add_atTop_nat 1)).eventually_lt_const (by norm_num : (0:ℝ)<1)
  have hall : ∀ᶠ n : ℕ in atTop, 64 ≤ n+1 ∧ beta (n+1)<1 ∧ tailEnvelope (n+1) eps < eta := by
    filter_upwards [eventually_ge_atTop (63:ℕ), hb, he] with n hn hbn hen
    exact ⟨by omega,hbn,hen⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hall
  refine ⟨N,fun n hn H hdegree => ?_⟩
  obtain ⟨hm,hb,he⟩ := hN n hn
  have h := (normalized_tailEnvelope_bound H hdegree hm hb eps).trans he.le
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  exact (div_le_iff₀ hz).mp h

/-- Consequently any dimension-indexed family of actual deleted-degree-two graphs
has normalized tail tending to zero; the stronger uniform threshold is above. -/
theorem normalized_tail_tendsto (eps : ℝ) (heps : 0 < eps)
    (H : ∀ n : ℕ, SimpleGraph (Fin (n+1))) (hdegree : ∀ n i, (H n).degree i ≤ 2) :
    Tendsto (fun n => tailIntegral (H n) (window (n+1) eps)/Z (n+1) 1) atTop (𝓝 0) := by
  have he := (tendsto_tailEnvelope_zero eps heps).comp (tendsto_add_atTop_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · exact Filter.Eventually.of_forall (fun n =>
      div_nonneg (tailIntegral_nonneg _ _) (partition_pos n 1 (by norm_num)).le)
  · have hb := (tendsto_beta_zero.comp (tendsto_add_atTop_nat 1)).eventually_lt_const (by norm_num : (0:ℝ)<1)
    filter_upwards [eventually_ge_atTop (63:ℕ), hb] with n hn hbn
    exact normalized_tailEnvelope_bound (H n) (hdegree n) (by omega) hbn eps

/-- The complete intended endpoint, exposing the actual closed-box Lebesgue integral
and the literal sqrt(m)(2π/m)^((m-1)/2) normalization rather than a proxy constant. -/
theorem uniform_deleted_torus_tail_explicit (eps : ℝ) (heps : 0 < eps) :
    ∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SimpleGraph (Fin (n+1)), (∀ i, H.degree i ≤ 2) →
        (∫ z in Set.univ.pi (fun _ : Fin n => Icc (-Real.pi/2) (Real.pi/2)),
          ({z | ∃ i, ((n+1 : ℕ) : ℝ)^(-(1:ℝ)/2+eps) < |z i|} : Set (Fin n → ℝ)).indicator
            (fun z => kernel H (Fin.cons 0 z)) z) ≤
          eta * (Real.sqrt (n+1 : ℕ) *
            (2*Real.pi/((n+1 : ℕ) : ℝ))^((((n+1 : ℕ) : ℝ)-1)/2)) := by
  intro eta heta
  obtain ⟨N,hN⟩ := uniform_deleted_torus_tail eps heps eta heta
  refine ⟨max N 1,fun n hn H hdegree => ?_⟩
  have h := hN n ((le_max_left N 1).trans hn) H hdegree
  have hn1 : 1≤n := (le_max_right N 1).trans hn
  rw [Z_one_rpow (n+1) (by omega)] at h
  simpa only [tailIntegral, window, realBad, boxMeasure_eq_closed,
    show -Real.pi/2+Real.pi=Real.pi/2 by ring] using h

end UniformTorusTail
