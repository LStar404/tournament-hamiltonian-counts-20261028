module

public import TournamentHamiltonian.Equality.PrefixEquality
public import Mathlib.Order.UpperLower.Basic

@[expose] public section

set_option autoImplicit false

namespace TournamentHamiltonian.Equality

/-- The actual finite maximum over the r=0,...,n prefix expressions. The zero
prefix is included, so this is defined also for n=0 without an artificial bottom. -/
noncomputable def prefixTruncationMax {n : ℕ} (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) (fun r => finPrefixSum u r - (r : ℝ) * t)

/-- An antitone finite vector has an exact strict-threshold prefix. Neither
nonnegativity nor t>=0 is needed for this finite combinatorial identity. -/
theorem antitone_threshold_is_prefix {n : ℕ} (u : Fin n → ℝ) (hu : Antitone u) (t : ℝ) :
    ∃ r : ℕ, r ≤ n ∧ ∀ i : Fin n, t < u i ↔ i.val < r := by
  have hlow : IsLowerSet {i : Fin n | t < u i} := by
    intro i j hji hi
    exact lt_of_lt_of_le hi (hu hji)
  rcases hlow.eq_univ_or_Iio with hfull | ⟨a, ha⟩
  · refine ⟨n, le_rfl, ?_⟩
    intro i
    have hi : t < u i := by
      change i ∈ {i : Fin n | t < u i}
      rw [hfull]
      trivial
    exact iff_of_true hi i.isLt
  · refine ⟨a.val, Nat.le_of_lt a.isLt, ?_⟩
    intro i
    change (i ∈ {i : Fin n | t < u i}) ↔ i < a
    rw [ha]
    rfl

theorem prefix_sub_mul_eq_sum_sub {n : ℕ} (u : Fin n → ℝ) (t : ℝ)
    (r : ℕ) (hr : r ≤ n) :
    finPrefixSum u r - (r : ℝ) * t = ∑ i ∈ finPrefix n r, (u i - t) := by
  simp [finPrefixSum, Finset.sum_sub_distrib, finPrefix_card n r hr]

/-- No selected prefix can exceed the sum of all positive truncated coordinates. -/
theorem prefix_sub_mul_le_sum_truncated {n : ℕ} (u : Fin n → ℝ) (t : ℝ)
    (r : ℕ) (hr : r ≤ n) :
    finPrefixSum u r - (r : ℝ) * t ≤ ∑ i, max (u i - t) 0 := by
  rw [prefix_sub_mul_eq_sum_sub u t r hr]
  calc
    _ ≤ ∑ i ∈ finPrefix n r, max (u i - t) 0 :=
      Finset.sum_le_sum (fun i _ => le_max_left _ _)
    _ ≤ ∑ i, max (u i - t) 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => le_max_right _ _)

/-- The strict-threshold prefix attains the truncated sum exactly. -/
theorem sum_truncated_eq_threshold_prefix {n : ℕ} (u : Fin n → ℝ) (t : ℝ)
    (r : ℕ) (hr : r ≤ n) (hcut : ∀ i : Fin n, t < u i ↔ i.val < r) :
    (∑ i, max (u i - t) 0) = finPrefixSum u r - (r : ℝ) * t := by
  rw [prefix_sub_mul_eq_sum_sub u t r hr]
  simp only [finPrefix, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · rw [ite_eq_left hi, max_eq_left (sub_nonneg.mpr ((hcut i).mpr hi).le)]
  · have hle : u i ≤ t := le_of_not_gt (fun h => hi ((hcut i).mp h))
    rw [ite_eq_right hi, max_eq_right (sub_nonpos.mpr hle)]

/-- Literal equality between the truncated sum and the maximum of finite prefix
expressions, rather than just the squared-norm consequence. -/
theorem sum_truncated_eq_prefixTruncationMax {n : ℕ}
    (u : Fin n → ℝ) (hu : Antitone u) (t : ℝ) :
    (∑ i, max (u i - t) 0) = prefixTruncationMax u t := by
  obtain ⟨r, hr, hcut⟩ := antitone_threshold_is_prefix u hu t
  apply le_antisymm
  · rw [sum_truncated_eq_threshold_prefix u t r hr hcut]
    exact Finset.le_sup' (fun r => finPrefixSum u r - (r : ℝ) * t)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · apply Finset.sup'_le
    intro r hr
    exact prefix_sub_mul_le_sum_truncated u t r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))

/-- Prefix domination controls the actual finite maxima at every real threshold. -/
theorem prefixTruncationMax_le_of_finPrefix_le {n : ℕ} (u v : Fin n → ℝ)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) (t : ℝ) :
    prefixTruncationMax u t ≤ prefixTruncationMax v t := by
  apply Finset.sup'_le
  intro r hr
  exact (sub_le_sub_right (hprefix r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))) _).trans
    (Finset.le_sup' (fun r => finPrefixSum v r - (r : ℝ) * t) hr)

/-- The manuscript's entire equality/inequality/equality chain, proved in a
slightly stronger form allowing any real threshold and arbitrary antitone vectors. -/
theorem truncated_prefix_max_chain {n : ℕ} (u v : Fin n → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) (t : ℝ) :
    (∑ i, max (u i - t) 0) = prefixTruncationMax u t ∧
    prefixTruncationMax u t ≤ prefixTruncationMax v t ∧
    prefixTruncationMax v t = ∑ i, max (v i - t) 0 :=
  ⟨sum_truncated_eq_prefixTruncationMax u hu t,
    prefixTruncationMax_le_of_finPrefix_le u v hprefix t,
    (sum_truncated_eq_prefixTruncationMax v hv t).symm⟩

/-- The resulting actual truncated-sum monotonicity includes n=0 and threshold ties. -/
theorem sum_truncated_le_of_finPrefix_le {n : ℕ} (u v : Fin n → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) (t : ℝ) :
    (∑ i, max (u i - t) 0) ≤ ∑ i, max (v i - t) 0 := by
  rw [sum_truncated_eq_prefixTruncationMax u hu t, sum_truncated_eq_prefixTruncationMax v hv t]
  exact prefixTruncationMax_le_of_finPrefix_le u v hprefix t

/-- Lemma 6.3 with its literal nonnegative/decreasing and nonnegative-threshold
hypotheses; the proof above also establishes the stronger unrestricted-threshold form. -/
theorem truncated_sums_under_weak_majorization {n : ℕ} (u v : Fin n → ℝ)
    (hu : DecreasingNonneg u) (hv : DecreasingNonneg v)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r)
    (t : ℝ) (_ht : 0 ≤ t) :
    (∑ i, max (u i - t) 0) = prefixTruncationMax u t ∧
    prefixTruncationMax u t ≤ prefixTruncationMax v t ∧
    prefixTruncationMax v t = ∑ i, max (v i - t) 0 :=
  truncated_prefix_max_chain u v hu.2 hv.2 hprefix t

end TournamentHamiltonian.Equality
