module

public import TournamentHamiltonian.UniformTorusTail.Cover
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Per-outlier loss after the exact Gaussian dimension ratio. -/
def q (m : ℕ) : ℝ := Real.pi * Real.sqrt (Real.exp 1*m/(2*Real.pi)) * Real.exp (-kappa1*m/2)
/-- This is algebraically sqrt(eπ/2) m^(3/2) exp(-κ₁m/2). -/
def beta (m : ℕ) : ℝ := m*q m

lemma q_nonneg (m : ℕ) : 0 ≤ q m := by unfold q; positivity
lemma beta_nonneg (m : ℕ) : 0 ≤ beta m := mul_nonneg (Nat.cast_nonneg _) (q_nonneg _)

lemma geometric_tail_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (m : ℕ) :
    (∑ r ∈ Finset.range m, b^(r+1)) ≤ b/(1-b) := by
  have h := (summable_geometric_of_lt_one hb0 hb1).sum_le_tsum
    (Finset.range m) (fun i _ => pow_nonneg hb0 i)
  rw [tsum_geometric_of_lt_one hb0 hb1] at h
  have hh := mul_le_mul_of_nonneg_left h hb0
  simpa only [pow_succ', ← Finset.mul_sum, div_eq_mul_inv] using hh

/-- A finite combinatorial sum bound derived from actual subsets and choose≤m^r. -/
theorem nonempty_subset_geometric_bound (m : ℕ) (v : ℝ) (hv : 0 ≤ v)
    (hsmall : (m : ℝ)*v < 1) :
    (∑ B : Finset (Fin m), if B.card=0 then (0:ℝ) else v^B.card) ≤
      ((m : ℝ)*v)/(1-(m : ℝ)*v) := by
  have he : (Finset.univ : Finset (Finset (Fin m))) = (Finset.univ : Finset (Fin m)).powerset := by
    ext B; simp
  rw [he, Finset.sum_powerset_apply_card (fun r => if r=0 then (0:ℝ) else v^r)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, pow_zero,
    ite_true, mul_zero, add_zero]
  apply le_trans _ (geometric_tail_bound ((m : ℝ)*v) (by positivity) hsmall m)
  apply Finset.sum_le_sum
  intro r _
  have hc : (m.choose (r+1) : ℝ) ≤ (m : ℝ)^(r+1) := by exact_mod_cast Nat.choose_le_pow m (r+1)
  simpa only [mul_pow] using mul_le_mul_of_nonneg_right hc (pow_nonneg hv (r+1))

lemma normalization_outlier_term (m r : ℕ) (hp : 2 ≤ m-r) :
    Real.pi^r * Z (m-r) 1 * Real.exp (-kappa1*(m : ℝ)*r/2) ≤ Z m 1*(q m)^r := by
  have hz : 0 < Z m 1 := partition_pos (m-1) 1 (by norm_num)
  have hrat := (div_le_iff₀ hz).mp (Z_deletion_ratio m r hp)
  have hbase : 0 ≤ Real.exp 1*(m : ℝ)/(2*Real.pi) := by positivity
  have hsqrt : (Real.exp 1*(m : ℝ)/(2*Real.pi))^((r : ℝ)/2) =
      (Real.sqrt (Real.exp 1*(m : ℝ)/(2*Real.pi)))^r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hbase]
    congr 1
    ring
  have hexp : Real.exp (-kappa1*(m : ℝ)*r/2) = (Real.exp (-kappa1*m/2))^r := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsqrt] at hrat
  have h := mul_le_mul_of_nonneg_left hrat
    (show 0 ≤ Real.pi^r*Real.exp (-kappa1*(m : ℝ)*r/2) by positivity)
  rw [hexp] at h
  unfold q
  rw [hexp, mul_pow, mul_pow]
  convert h using 1 <;> ring

/-- The actual sum over possible outlier index sets has the planned geometric loss. -/
theorem outlierSum_bound (m : ℕ) (hm : 64 ≤ m) (hb : beta m < 1) :
    outlierSum m ≤ Z m 1 * (beta m/(1-beta m)) := by
  have hterm (B : Finset (Fin m)) (hB : B ∈ outlierSets m) :
      Real.pi^B.card*Z (m-B.card) 1*Real.exp (-kappa1*(m : ℝ)*B.card/2) ≤ Z m 1*(q m)^B.card := by
    have hc := large_complement hm B (Finset.mem_filter.mp hB).2.2
    simp only [Finset.card_compl, Fintype.card_fin] at hc
    exact normalization_outlier_term m B.card (by omega)
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hs
  have hzero : (∑ B ∈ outlierSets m, (q m)^B.card) =
      ∑ B ∈ outlierSets m, if B.card=0 then (0:ℝ) else (q m)^B.card := by
    apply Finset.sum_congr rfl
    intro B hB
    rw [ite_eq_right (Nat.ne_of_gt (Finset.mem_filter.mp hB).2.1)]
  rw [hzero] at hs
  have hext : (∑ B ∈ outlierSets m, if B.card=0 then (0:ℝ) else (q m)^B.card) ≤
      ∑ B : Finset (Fin m), if B.card=0 then (0:ℝ) else (q m)^B.card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro B _ _
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (q_nonneg m) _
  have hg := nonempty_subset_geometric_bound m (q m) (q_nonneg m) hb
  exact hs.trans (mul_le_mul_of_nonneg_left (hext.trans hg) (partition_pos (m-1) 1 (by norm_num)).le)

/-- Planned explicit finite normalized bound for the actual deleted-graph torus tail. -/
theorem normalized_tail_bound {n : ℕ} (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ n+1) (hb : beta (n+1) < 1)
    (t : ℝ) (ht : 0 ≤ t) :
    tailIntegral H t / Z (n+1) 1 ≤
      16 * Real.pi^n/Z (n+1) 1 * farConstant (n+1) +
      16*Real.exp 4*(beta (n+1)/(1-beta (n+1))) +
      32*Real.exp 4*n*Real.exp (-((n+1 : ℝ)-4)*t^2/4) := by
  have h := tailIntegral_subset_bound H hdegree hm t ht
  have ho := outlierSum_bound (n+1) hm hb
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  apply (div_le_iff₀ hz).mpr
  have hmul := mul_le_mul_of_nonneg_left ho (show 0 ≤ 16*Real.exp 4 by positivity)
  have he : (16 * Real.pi^n/Z (n+1) 1 * farConstant (n+1) +
      16*Real.exp 4*(beta (n+1)/(1-beta (n+1))) +
      32*Real.exp 4*n*Real.exp (-((n+1 : ℝ)-4)*t^2/4))*Z (n+1) 1 =
      16*(Real.pi^n*farConstant (n+1) + Real.exp 4*(Z (n+1) 1*(beta (n+1)/(1-beta (n+1)))) +
        2*n*Real.exp 4*Z (n+1) 1*Real.exp (-((n+1 : ℝ)-4)*t^2/4)) := by
    field_simp; ring
  rw [he]
  nlinarith

end UniformTorusTail
