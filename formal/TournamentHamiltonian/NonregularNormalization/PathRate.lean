module

public import TournamentHamiltonian.NonregularNormalization.AugmentedScalar

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa NonregularRate NonregularDecay
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem augmentMatrix_box {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1) :
    ∀ i j, 0 ≤ augmentMatrix A i j ∧ augmentMatrix A i j ≤ 1 := by
  intro i j
  refine Fin.cases ?_ (fun a => ?_) i
  · exact Fin.cases (by norm_num [augmentMatrix]) (fun _ => by norm_num) j
  · exact Fin.cases (by norm_num) (fun b => hA a b) j

theorem augmentMatrix_row_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, augmentMatrix A 0 j = (n : ℝ)/2 := by
  rw [Fin.sum_univ_succ]
  simp [augmentMatrix]
  ring

theorem augmentMatrix_row_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ j, augmentMatrix A i.succ j = 1/2 + ∑ j, A i j := by
  rw [Fin.sum_univ_succ]
  simp

/-- Actual augmented permanent bound whenever the original matrix has the
proved block row sums. The new row target is N and old targets are ceil(mb+1/2). -/
theorem augmented_permanent_le {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d)
    (e : Arrangement d m) (A : Matrix (Fin (d*m)) (Fin (d*m)) ℝ)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hrow : ∀ i, ∑ j, A i j = (m : ℝ)*baseB T (e i).1-1/2) :
    (augmentMatrix A).permanent ≤ augBlockBregman T m := by
  have hN : 1 ≤ d*m := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  let Q : Fin (d*m+1) → ℕ := Fin.cases (d*m) (fun i => augRowTarget T m (e i).1)
  have hQ (i : Fin (d*m+1)) : 1 ≤ Q i ∧ Q i ≤ d*m+1 := by
    refine Fin.cases ⟨hN, Nat.le_succ _⟩ (fun v => ?_) i
    exact ⟨(augRowTarget_spec hd hm T (e v).1).1,
      (augRowTarget_spec hd hm T (e v).1).2.1.trans (Nat.le_succ _)⟩
  have hsum (i : Fin (d*m+1)) : ∑ j, augmentMatrix A i j ≤ Q i := by
    refine Fin.cases ?_ (fun v => ?_) i
    · rw [augmentMatrix_row_zero]
      change (↑(d*m) : ℝ)/2 ≤ ↑(d*m)
      have h0 : (0 : ℝ) ≤ (d*m : ℕ) := Nat.cast_nonneg _
      linarith
    · rw [augmentMatrix_row_succ, hrow]
      change (1/2 : ℝ)+((m : ℝ)*baseB T (e v).1-1/2) ≤ augRowTarget T m (e v).1
      linarith [(augRowTarget_spec hd hm T (e v).1).2.2.2.1]
  have h := weighted_permanent_le_factorial_product (augmentMatrix A) Q hQ (augmentMatrix_box A hA) hsum
  have he : (∏ i, ((Q i).factorial : ℝ)^((1 : ℝ)/Q i)) = augBlockBregman T m := by
    rw [Fin.prod_univ_succ]
    dsimp only [Q, Fin.cases_zero, Fin.cases_succ]
    have hre := Equiv.prod_comp e (fun u : Vertex d m =>
      ((augRowTarget T m u.1).factorial : ℝ)^((1 : ℝ)/augRowTarget T m u.1))
    rw [hre, grouped_factorial_product]
    have hf : (((d*m).factorial : ℝ)^((1 : ℝ)/(d*m))) =
        Real.exp (Real.log (((d*m).factorial) : ℝ)/(d*m)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    simp only [Nat.cast_mul]
    rw [hf, blockBregman, augBlockBregman, Real.exp_add]
    ring
  exact h.trans_eq he

theorem meanPaths_eq_four_meanCycles_succ {n : ℕ} (hn : 1 ≤ n) :
    meanPaths n = 4*meanCycles (n+1) := by
  rw [meanPaths, meanCycles, Nat.add_sub_cancel]
  have hp : (2 : ℝ)^(n+1) = 4*(2 : ℝ)^(n-1) := by
    rw [show n+1 = (n-1)+2 by omega, pow_add]
    norm_num
    ring
  rw [hp]
  field_simp

/-- The exact §11.6 uniform expected-path rate, via a proved monomial injection. -/
theorem uniform_path_rate {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    avgPath (m := m) T / meanPaths (d*m) ≤
      2*Real.exp (11*(d : ℝ)/3+1/12) * (2*Real.pi)^(2*d+1) *
        ((d*m : ℝ)+1)^(2*d+2) * kappa T^(d*m) := by
  have hN : 1 ≤ d*m := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  let e := vertexEquiv d m
  have hp := uniform_avgPath_div_four_le_augmented_permanent hN T e
  have hb := augmented_permanent_le hd hm T e ((uniformMatrix (m := m) T).submatrix e e)
    (fun i j => uniform_weight_box T (e i) (e j)) (fun i => by
      change (∑ j, weight T (e i) (e j)) = _
      rw [Equiv.sum_comp e (fun v => weight T (e i) v)]
      exact uniform_weight_row_sum T (e i))
  have he : avgPath (m := m) T / meanPaths (d*m) =
      (avgPath (m := m) T/4)/meanCycles (d*m+1) := by
    rw [meanPaths_eq_four_meanCycles_succ hN]
    ring
  rw [he]
  exact (div_le_div_of_nonneg_right (hp.trans hb) (meanCycles_pos _).le).trans (augBlockBregman_path_rate hd hm T)

/-- The exact path bound for each actual regular-block sample. -/
theorem regular_sample_path_rate {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ 2*k+1)
    (T : Tournament d) (ω : RegularSample d k) :
    (pathCount T (regularSampleBits ω) : ℝ) / meanPaths (d*(2*k+1)) ≤
      2*Real.exp (11*(d : ℝ)/3+1/12) * (2*Real.pi)^(2*d+1) *
        ((d*(2*k+1) : ℝ)+1)^(2*d+2) * kappa T^(d*(2*k+1)) := by
  have hN : 1 ≤ d*(2*k+1) := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  let e := vertexEquiv d (2*k+1)
  rw [pathCount_eq_existing T (regularSampleBits ω) e]
  have hp := actual_pathCount_div_four_le_augmented_permanent hN (regularBlowup T ω e)
  have hb := augmented_permanent_le hd hk T e (adjacency (regularBlowup T ω e))
    (fun i j => by unfold adjacency; split_ifs <;> norm_num) (fun i => by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using regular_adjacency_row_sum T ω e i)
  have he : (TournamentHamiltonian.pathCount (regularBlowup T ω e) : ℝ)/meanPaths (d*(2*k+1)) =
      ((TournamentHamiltonian.pathCount (regularBlowup T ω e) : ℝ)/4)/meanCycles (d*(2*k+1)+1) := by
    rw [meanPaths_eq_four_meanCycles_succ hN]
    ring
  change (TournamentHamiltonian.pathCount (regularBlowup T ω e) : ℝ)/meanPaths (d*(2*k+1)) ≤ _
  rw [he]
  apply (div_le_div_of_nonneg_right (hp.trans hb) (meanCycles_pos _).le).trans
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using augBlockBregman_path_rate hd hk T

/-- The exact §11.6 regular expected-path rate over its nonempty odd-size model. -/
theorem regular_path_rate {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ 2*k+1) (T : Tournament d) :
    regularAvgPath T k / meanPaths (d*(2*k+1)) ≤
      2*Real.exp (11*(d : ℝ)/3+1/12) * (2*Real.pi)^(2*d+1) *
        ((d*(2*k+1) : ℝ)+1)^(2*d+2) * kappa T^(d*(2*k+1)) := by
  rw [regularAvgPath, div_right_comm, Finset.sum_div]
  apply finite_average_le (regularSample_card_pos d k)
  exact regular_sample_path_rate hd hk T

end
end NonregularNormalization
