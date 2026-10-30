module

public import TournamentHamiltonian.SubsetWeights
public import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

@[expose] public section
open Filter
open scoped Topology
namespace TournamentHamiltonian

/-- Dense Hadamard coefficient, with the correct empty-size value `1`. -/
noncomputable def denseHadamardWeight (k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) ^ k) / Nat.factorial k

theorem denseHadamardWeight_nonneg (k : ℕ) : 0 ≤ denseHadamardWeight k := by
  unfold denseHadamardWeight
  positivity

@[simp] theorem denseHadamardWeight_zero : denseHadamardWeight 0 = 1 := by
  norm_num [denseHadamardWeight]

theorem denseHadamardWeight_eq_rpow (k : ℕ) :
    denseHadamardWeight k = (k : ℝ) ^ ((k : ℝ) / 2) / Nat.factorial k := by
  unfold denseHadamardWeight
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]
  congr 2
  ring

/-- The existing all-order subset-weight ratio theorem also controls dense minors. -/
theorem denseHadamardWeight_le_subsetWeight (k : ℕ) :
    denseHadamardWeight k ≤ subsetWeight k := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.sqrt_le_sqrt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg k) (by linarith [Nat.cast_nonneg (α := ℝ) k]) k

/-- An explicit summable envelope, including an arbitrary fixed polynomial degree.
No summability premise is used: this invokes the certified all-order ratio estimate. -/
noncomputable def denseTailEnvelope (A : ℝ) (r k : ℕ) : ℝ :=
  (1 + (k : ℝ) ^ r) * A ^ k * subsetWeight k

theorem denseTailEnvelope_nonneg {A : ℝ} (hA : 0 ≤ A) (r k : ℕ) :
    0 ≤ denseTailEnvelope A r k := by
  unfold denseTailEnvelope
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hA _)) (subsetWeight_nonneg _)

theorem denseTailEnvelope_summable {A : ℝ} (hA : 0 ≤ A) (r : ℕ) :
    Summable (denseTailEnvelope A r) := by
  convert (subsetMoment_summable hA 0).add (subsetMoment_summable hA r) using 1
  ext k
  simp [denseTailEnvelope, subsetMoment]
  ring

theorem denseHadamardMoment_le_envelope {A : ℝ} (hA : 0 ≤ A) (r k : ℕ) :
    (1 + (k : ℝ) ^ r) * A ^ k * denseHadamardWeight k ≤ denseTailEnvelope A r k := by
  exact mul_le_mul_of_nonneg_left (denseHadamardWeight_le_subsetWeight k) (by positivity)

theorem denseHadamardMoment_summable {A : ℝ} (hA : 0 ≤ A) (r : ℕ) :
    Summable (fun k : ℕ => (1 + (k : ℝ) ^ r) * A ^ k * denseHadamardWeight k) := by
  exact Summable.of_nonneg_of_le (fun k => by
    exact mul_nonneg (by positivity) (denseHadamardWeight_nonneg k))
    (denseHadamardMoment_le_envelope hA r) (denseTailEnvelope_summable hA r)

theorem denseHadamardRpowMoment_summable {A : ℝ} (hA : 0 ≤ A) (r : ℕ) :
    Summable (fun k : ℕ => (1 + (k : ℝ) ^ r) * A ^ k *
      ((k : ℝ) ^ ((k : ℝ) / 2) / Nat.factorial k)) := by
  simpa only [denseHadamardWeight_eq_rpow] using denseHadamardMoment_summable hA r

/-- Finite triangular sums: bounds are needed only above a fixed ambient cutoff,
and only inside the actual triangle. This is a theorem, not an assumed limit rule. -/
theorem tendsto_triangular_sum_zero_of_summable
    (e : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (N₀ : ℕ)
    (hb : ∀ k, 0 ≤ b k) (hs : Summable b)
    (hlim : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0))
    (hbound : ∀ n, N₀ ≤ n → ∀ k, k ≤ n → |e n k| ≤ b k) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n+1), e n k) atTop (𝓝 0) := by
  let f : ℕ → ℕ → ℝ := fun n k => if k ≤ n then e n k else 0
  have hf : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 0) := by
    intro k
    apply (hlim k).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    simp [f, hn]
  have hfb : ∀ᶠ n in atTop, ∀ k, ‖f n k‖ ≤ b k := by
    filter_upwards [eventually_ge_atTop N₀] with n hn
    intro k
    by_cases hk : k ≤ n
    · simpa [f, hk, Real.norm_eq_abs] using hbound n hn k hk
    · simpa [f, hk] using hb k
  have ht := tendsto_tsum_of_dominated_convergence hs hf hfb
  have heq (n : ℕ) : (∑' k, f n k) = ∑ k ∈ Finset.range (n+1), e n k := by
    rw [tsum_eq_sum (s := Finset.range (n+1)) (by
      intro k hk
      simp only [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk
      simp [f, Nat.not_le.mpr hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    simp [f, hk]
  simpa only [heq, tsum_zero] using ht

/-- Ready-to-use dense-envelope specialization; the only analytic input remaining
is fixed-size convergence, not an unproved summability certificate. -/
theorem tendsto_triangular_sum_zero_of_dense_envelope
    (e : ℕ → ℕ → ℝ) (A C : ℝ) (r N₀ : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hlim : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0))
    (hbound : ∀ n, N₀ ≤ n → ∀ k, k ≤ n →
      |e n k| ≤ C * denseTailEnvelope A r k) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n+1), e n k) atTop (𝓝 0) := by
  exact tendsto_triangular_sum_zero_of_summable e _ N₀
    (fun k => mul_nonneg hC (denseTailEnvelope_nonneg hA r k))
    ((denseTailEnvelope_summable hA r).mul_left C) hlim hbound

end TournamentHamiltonian
