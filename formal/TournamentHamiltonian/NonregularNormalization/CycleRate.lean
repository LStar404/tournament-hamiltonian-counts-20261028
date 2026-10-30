module

public import TournamentHamiltonian.NonregularNormalization.ScalarRate
public import TournamentHamiltonian.NonregularDecay.ExpectationDecay

@[expose] public section

set_option autoImplicit false
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa NonregularRate NonregularDecay
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual expected adjacency matrix from the frozen uniform model. -/
def uniformMatrix {d m : ℕ} (T : Tournament d) : Matrix (Vertex d m) (Vertex d m) ℝ := weight T

theorem grouped_factorial_product {d m : ℕ} (R : Fin d → ℕ) :
    (∏ u : Vertex d m, ((R u.1).factorial : ℝ)^((1 : ℝ)/R u.1)) = blockBregman R m := by
  rw [Fintype.prod_prod_type, blockBregman, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_nat_mul]
  congr 1
  ring

theorem uniform_permanent_le_blockBregman {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    (uniformMatrix (m := m) T).permanent ≤ blockBregman (rowTarget T m) m := by
  have h := weighted_permanent_le_factorial_product_fintype (uniformMatrix (m := m) T)
    (fun u => rowTarget T m u.1)
    (fun u => ⟨(rowTarget_spec hd hm T u.1).1, by simpa using (rowTarget_spec hd hm T u.1).2.1⟩)
    (uniform_weight_box T) (fun u => by
      change (∑ v, weight T u v) ≤ _
      rw [uniform_weight_row_sum]
      exact (rowTarget_spec hd hm T u.1).2.2.2.1)
  simpa only [grouped_factorial_product] using h

/-- Genuine full single-cycle weights form a subset of all nonnegative
permanent monomials. No independence is asserted for general cycle covers. -/
theorem weightedCycleSum_le_permanent {d m : ℕ} (T : Tournament d) :
    weightedCycleSum (m := m) T ≤ (uniformMatrix (m := m) T).permanent := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  unfold weightedCycleSum cycleWeight
  change (∑ σ : Cycle d m, ∏ u : Vertex d m, weight T u (σ.val u)) ≤
    ∑ σ : Equiv.Perm (Vertex d m), ∏ u : Vertex d m, weight T u (σ u)
  apply Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
    (f := fun σ : Cycle d m => ∏ u : Vertex d m, weight T u (σ.val u))
    (g := fun σ : Equiv.Perm (Vertex d m) => ∏ u : Vertex d m, weight T u (σ u))
    Subtype.val Subtype.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
  intro σ _ _
  exact Finset.prod_nonneg fun u _ => (uniform_weight_box T u (σ u)).1

/-- The exact §11.5 uniform-model cycle bound with its printed constants. -/
theorem uniform_cycle_rate {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (hN : 3 ≤ d*m)
    (T : Tournament d) :
    avgCycle (m := m) T / meanCycles (d*m) ≤
      Real.exp (8*(d : ℝ)/3) * (2*Real.pi)^(2*d) * (d*m : ℝ)^(2*d+1) * kappa T^(d*m) := by
  rw [avgCycle_eq_weightedCycleSum hN]
  apply (div_le_div_of_nonneg_right
    ((weightedCycleSum_le_permanent T).trans (uniform_permanent_le_blockBregman hd hm T))
    (meanCycles_pos _).le).trans
  exact blockBregman_cycle_rate hd hm T

/-- Exact regular-block adjacency rows, identified through the actual blowup
score bridge rather than through independent-edge expectations. -/
theorem regular_adjacency_row_sum {d k : ℕ} (T : Tournament d) (ω : RegularSample d k)
    (e : Arrangement d (2*k+1)) (v : Fin (d*(2*k+1))) :
    ∑ j, adjacency (regularBlowup T ω e) v j =
      (2*k+1 : ℝ)*baseB T (e v).1-1/2 := by
  have hs := NonregularDecay.score_blowup T (regularSampleBits ω) e (e v)
  simp only [Equiv.symm_apply_apply] at hs
  have hreg : score ((blockTournamentEquiv d (2*k+1)) (regularSampleBits ω) (e v).1) (e v).2 = 0 := by
    simp only [regularSampleBits, Equiv.apply_symm_apply]
    exact (ω (e v).1).property (e v).2
  rw [hreg, add_zero] at hs
  rw [← outDegree_eq_sum_adjacency]
  change (outDegree (blowup T (regularSampleBits ω) e) v : ℝ) = _
  rw [score_eq_outDegree, score_eq_outDegree] at hs
  dsimp [baseB]
  push_cast at hs ⊢
  linarith

theorem regular_permanent_le_blockBregman {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ 2*k+1)
    (T : Tournament d) (ω : RegularSample d k) (e : Arrangement d (2*k+1)) :
    (adjacency (regularBlowup T ω e)).permanent ≤ blockBregman (rowTarget T (2*k+1)) (2*k+1) := by
  have h := weighted_permanent_le_factorial_product (adjacency (regularBlowup T ω e))
    (fun v => rowTarget T (2*k+1) (e v).1)
    (fun v => ⟨(rowTarget_spec hd hk T (e v).1).1, (rowTarget_spec hd hk T (e v).1).2.1⟩)
    (fun i j => by unfold adjacency; split_ifs <;> norm_num)
    (fun v => by
      rw [regular_adjacency_row_sum]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using (rowTarget_spec hd hk T (e v).1).2.2.2.1)
  have he := Equiv.prod_comp e (fun u : Vertex d (2*k+1) =>
    ((rowTarget T (2*k+1) u.1).factorial : ℝ)^((1 : ℝ)/rowTarget T (2*k+1) u.1))
  rw [he] at h
  simpa only [grouped_factorial_product] using h

/-- The same printed cycle bound holds for every actual regular-block sample. -/
theorem regular_sample_cycle_rate {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ 2*k+1)
    (T : Tournament d) (ω : RegularSample d k) :
    (cycleCount T (regularSampleBits ω) : ℝ) / meanCycles (d*(2*k+1)) ≤
      Real.exp (8*(d : ℝ)/3) * (2*Real.pi)^(2*d) *
        (d*(2*k+1) : ℝ)^(2*d+1) * kappa T^(d*(2*k+1)) := by
  have h := (cycleCount_le_permanent T (regularSampleBits ω) (vertexEquiv d (2*k+1))).trans
    (regular_permanent_le_blockBregman hd hk T ω (vertexEquiv d (2*k+1)))
  apply (div_le_div_of_nonneg_right h (meanCycles_pos _).le).trans
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using blockBregman_cycle_rate hd hk T

/-- The exact §11.5 regular-model cycle expectation bound, averaging only over
the already proved nonempty product of regular tournaments at odd sizes. -/
theorem regular_cycle_rate {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ 2*k+1) (T : Tournament d) :
    regularAvgCycle T k / meanCycles (d*(2*k+1)) ≤
      Real.exp (8*(d : ℝ)/3) * (2*Real.pi)^(2*d) *
        (d*(2*k+1) : ℝ)^(2*d+1) * kappa T^(d*(2*k+1)) := by
  rw [regularAvgCycle, div_right_comm, Finset.sum_div]
  apply finite_average_le (regularSample_card_pos d k)
  exact regular_sample_cycle_rate hd hk T

end
end NonregularNormalization
