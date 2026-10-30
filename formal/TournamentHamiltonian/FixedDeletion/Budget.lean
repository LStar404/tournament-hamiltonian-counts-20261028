module

public import TournamentHamiltonian.DensePathConvergence

@[expose] public section

set_option autoImplicit false
namespace FixedDeletion
open TournamentHamiltonian Filter
open scoped BigOperators Topology
noncomputable section

/-- Shifted scalar errors. The definition is total even for j+k>n; it is only
applied to actual deletion ratios when the corresponding disjoint set exists. -/
def shiftBudget (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), denseCountWeight j *
    (denseRatioErrorBudget n (j+k) + denseRatioErrorBudget n j)

def hitBudget (k n : ℕ) : ℝ :=
  ((k : ℝ)/n) * ∑ j ∈ Finset.range (n+1),
    (j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j

def budget (k n : ℕ) : ℝ := shiftBudget k n + hitBudget k n

theorem shiftBudget_nonneg (k n : ℕ) : 0 ≤ shiftBudget k n := by
  unfold shiftBudget
  exact Finset.sum_nonneg fun j _ => mul_nonneg (denseCountWeight_nonneg j)
    (add_nonneg (denseRatioErrorBudget_nonneg n _) (denseRatioErrorBudget_nonneg n _))

theorem hitBudget_nonneg (k n : ℕ) : 0 ≤ hitBudget k n := by
  have hC := denseGlobalRatioPrefactor_one_le
  have ha := denseGlobalRatioBase_one_le
  unfold hitBudget
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun j _ => by positivity [denseCountWeight_nonneg j]

theorem budget_nonneg (k n : ℕ) : 0 ≤ budget k n :=
  add_nonneg (shiftBudget_nonneg k n) (hitBudget_nonneg k n)

theorem shift_envelope (n j k : ℕ) :
    denseCountWeight j*(denseRatioErrorBudget n (j+k)+denseRatioErrorBudget n j) ≤
      ((denseGlobalRatioPrefactor+1)*(denseGlobalRatioBase^k+1)) *
        denseTailEnvelope (3*denseGlobalRatioBase) 1 j := by
  have ha : 0 ≤ denseGlobalRatioBase := le_trans (by norm_num) denseGlobalRatioBase_one_le
  have hC : 0 ≤ denseGlobalRatioPrefactor+1 := by linarith [denseGlobalRatioPrefactor_one_le]
  have hw := denseHadamardWeight_le_subsetWeight j
  calc
    _ ≤ denseCountWeight j *
        ((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^(j+k)+
          (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^j) :=
      mul_le_mul_of_nonneg_left (add_le_add (denseRatioErrorBudget_le_cap n _)
        (denseRatioErrorBudget_le_cap n _)) (denseCountWeight_nonneg j)
    _ ≤ ((1+(j : ℝ))*3^j*subsetWeight j) *
        ((denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^(j+k)+
          (denseGlobalRatioPrefactor+1)*denseGlobalRatioBase^j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by simp only [denseTailEnvelope, pow_one, pow_add, mul_pow]; ring

theorem shiftBudget_tendsto (k : ℕ) : Tendsto (shiftBudget k) atTop (𝓝 0) := by
  unfold shiftBudget
  apply tendsto_triangular_sum_zero_of_dense_envelope _
    (3*denseGlobalRatioBase) ((denseGlobalRatioPrefactor+1)*(denseGlobalRatioBase^k+1)) 1 0
  · linarith [denseGlobalRatioBase_one_le]
  · have := denseGlobalRatioBase_one_le; have := denseGlobalRatioPrefactor_one_le; positivity
  · intro j
    simpa using ((denseRatioErrorBudget_tendsto (j+k)).add
      (denseRatioErrorBudget_tendsto j)).const_mul (denseCountWeight j)
  · intro n _ j _
    rw [abs_of_nonneg (mul_nonneg (denseCountWeight_nonneg _)
      (add_nonneg (denseRatioErrorBudget_nonneg _ _) (denseRatioErrorBudget_nonneg _ _)))]
    exact shift_envelope n j k

theorem hit_envelope (k n j : ℕ) (hn : 1 ≤ n) :
    ((k : ℝ)/n) * ((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j) ≤
      (2*(k : ℝ)*denseGlobalRatioPrefactor)*denseTailEnvelope (3*denseGlobalRatioBase) 2 j := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hk : (k : ℝ)/n ≤ k := (div_le_iff₀ hn0).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hC : 0 ≤ denseGlobalRatioPrefactor := le_trans (by norm_num) denseGlobalRatioPrefactor_one_le
  have ha : 0 ≤ denseGlobalRatioBase := le_trans (by norm_num) denseGlobalRatioBase_one_le
  have hw := denseHadamardWeight_le_subsetWeight j
  have hj : (j : ℝ)*(1+j) ≤ 2*(1+(j : ℝ)^2) := by nlinarith [sq_nonneg ((j : ℝ)-1)]
  calc
    _ ≤ (k : ℝ) * ((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j) :=
      mul_le_mul_of_nonneg_right hk (by positivity [denseCountWeight_nonneg j])
    _ ≤ (k : ℝ) * ((j : ℝ)*((1+(j : ℝ))*3^j*subsetWeight j)*denseGlobalRatioPrefactor*denseGlobalRatioBase^j) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha _)
      apply mul_le_mul_of_nonneg_right _ hC
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) (Nat.cast_nonneg _)
    _ = ((j : ℝ)*(1+j))*((k : ℝ)*denseGlobalRatioPrefactor*(3*denseGlobalRatioBase)^j*subsetWeight j) := by
      rw [mul_pow]; ring
    _ ≤ (2*(1+(j : ℝ)^2))*((k : ℝ)*denseGlobalRatioPrefactor*(3*denseGlobalRatioBase)^j*subsetWeight j) :=
      mul_le_mul_of_nonneg_right hj (by positivity [subsetWeight_nonneg j])
    _ = _ := by unfold denseTailEnvelope; ring

theorem hitBudget_tendsto (k : ℕ) : Tendsto (hitBudget k) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n+1),
      ((k : ℝ)/n)*((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j)) atTop (𝓝 0) := by
    apply tendsto_triangular_sum_zero_of_dense_envelope _ (3*denseGlobalRatioBase)
      (2*(k : ℝ)*denseGlobalRatioPrefactor) 2 1
    · linarith [denseGlobalRatioBase_one_le]
    · have := denseGlobalRatioPrefactor_one_le; positivity
    · intro j
      simpa using (tendsto_natCast_atTop_atTop.const_div_atTop (k : ℝ)).mul_const
        ((j : ℝ)*denseCountWeight j*denseGlobalRatioPrefactor*denseGlobalRatioBase^j)
    · intro n hn j _
      have hC := denseGlobalRatioPrefactor_one_le
      have ha := denseGlobalRatioBase_one_le
      rw [abs_of_nonneg (by positivity [denseCountWeight_nonneg j])]
      exact hit_envelope k n j hn
  change Tendsto (fun n => hitBudget k n) atTop (𝓝 0)
  simpa only [hitBudget, Finset.mul_sum] using h

theorem budget_tendsto (k : ℕ) : Tendsto (budget k) atTop (𝓝 0) := by
  change Tendsto (fun n => budget k n) atTop (𝓝 0)
  simpa only [budget, add_zero] using (shiftBudget_tendsto k).add (hitBudget_tendsto k)

end
end FixedDeletion
