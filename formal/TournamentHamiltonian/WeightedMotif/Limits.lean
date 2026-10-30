module

public import TournamentHamiltonian.WeightedMotif.Scalars

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open TournamentHamiltonian UniformDeletion FiniteMotif Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A scalar triangular-array lemma: no shared random-variable space is used. -/
theorem tendsto_of_relative_errors {x b : ℕ → ℝ} {c : ℝ}
    (hb : Tendsto b atTop (𝓝 c))
    (he : ∀ ε : ℝ,0<ε → ∀ᶠ m in atTop,|x m-b m|≤ε*b m) :
    Tendsto x atTop (𝓝 c) := by
  have hd : Tendsto (fun m => x m-b m) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hK : 0< |c|+1 := by positivity
    have hbound : ∀ᶠ m in atTop,b m< |c|+1 :=
      (tendsto_order.mp hb).2 _ (by linarith [le_abs_self c])
    filter_upwards [he (ε/(|c|+1)) (div_pos hε hK),hbound] with m hm hbm
    rw [Real.dist_eq,sub_zero]
    calc |x m-b m| ≤ ε/(|c|+1)*b m := hm
      _ < ε/(|c|+1)*(|c|+1) := mul_lt_mul_of_pos_left hbm (div_pos hε hK)
      _ = ε := div_mul_cancel₀ _ hK.ne'
  simpa only [sub_add_cancel,zero_add] using hd.add hb

theorem cycle_mean_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleMean (m:=m) T) atTop (𝓝 (1/(d : ℝ))) := by
  apply tendsto_of_relative_errors (firstMain_tendsto d hd)
  intro ε hε
  filter_upwards [actual_moment_bounds T hT hd ε hε] with m h
  exact h.cycleFirst

theorem path_mean_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathMean (m:=m) T) atTop (𝓝 (1/(d : ℝ))) := by
  apply tendsto_of_relative_errors (firstMain_tendsto d hd)
  intro ε hε
  filter_upwards [actual_moment_bounds T hT hd ε hε] with m h
  exact h.pathFirst

theorem cycle_pair_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleDisjoint (m:=m) T) atTop (𝓝 ((1/(d : ℝ))^2)) := by
  apply tendsto_of_relative_errors (secondMain_tendsto d hd)
  intro ε hε
  filter_upwards [actual_moment_bounds T hT hd ε hε] with m h
  exact h.cyclePair

theorem path_pair_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathDisjoint (m:=m) T) atTop (𝓝 ((1/(d : ℝ))^2)) := by
  apply tendsto_of_relative_errors (secondMain_tendsto d hd)
  intro ε hε
  filter_upwards [actual_moment_bounds T hT hd ε hε] with m h
  exact h.pathPair

theorem cycle_overlap_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleOverlap (m:=m) T) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (overlap_budget_tendsto d)
  · filter_upwards [actual_moment_bounds T hT hd 1 (by norm_num)] with m h
    exact h.cycleOverlapBound.1
  · filter_upwards [actual_moment_bounds T hT hd 1 (by norm_num)] with m h
    exact h.cycleOverlapBound.2

theorem path_overlap_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathOverlap (m:=m) T) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (overlap_budget_tendsto d)
  · filter_upwards [actual_moment_bounds T hT hd 1 (by norm_num)] with m h
    exact h.pathOverlapBound.1
  · filter_upwards [actual_moment_bounds T hT hd 1 (by norm_num)] with m h
    exact h.pathOverlapBound.2

theorem cycle_second_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleSecond (m:=m) T) atTop (𝓝 ((1/(d : ℝ))^2)) := by
  simpa only [add_zero,←cycle_second_partition] using
    (cycle_pair_tendsto T hT hd).add (cycle_overlap_tendsto T hT hd)

theorem path_second_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathSecond (m:=m) T) atTop (𝓝 ((1/(d : ℝ))^2)) := by
  simpa only [add_zero,←path_second_partition] using
    (path_pair_tendsto T hT hd).add (path_overlap_tendsto T hT hd)

theorem centered_identity {α : Type*} [Fintype α] (w f : α → ℝ) (c : ℝ) (hZ : 0<total w) :
    expect w (fun x => (f x-c)^2)=expect w (fun x => (f x)^2)-2*c*expect w f+c^2 := by
  have h (x : α) : (f x-c)^2=(f x)^2+((-2*c)*f x+c^2) := by ring
  simp only [h,expect_add,expect_mul,expect_const w hZ]
  ring

/-- Numerical mean-square error for the genuine m-dependent cycle law. -/
def cycleMeanSquare {d m : ℕ} (T : Tournament d) : ℝ :=
  expect (cycleWeight (m:=m) T) (fun σ => ((cycleA σ : ℝ)/m-1/(d : ℝ))^2)
def pathMeanSquare {d m : ℕ} (T : Tournament d) : ℝ :=
  expect (pathWeight (m:=m) T) (fun π => ((pathA π : ℝ)/m-1/(d : ℝ))^2)

theorem cycle_meanSquare_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleMeanSquare (m:=m) T) atTop (𝓝 0) := by
  have h := ((cycle_second_tendsto T hT hd).sub
    ((cycle_mean_tendsto T hT hd).const_mul (2*(1/(d : ℝ))))).add_const ((1/(d : ℝ))^2)
  have hz : (1/(d : ℝ))^2-2*(1/(d : ℝ))*(1/(d : ℝ))+(1/(d : ℝ))^2=0 := by ring
  rw [hz] at h
  apply h.congr'
  filter_upwards [actual_positive T hT hd] with m hm
  exact (centered_identity _ _ _ hm.1).symm

theorem path_meanSquare_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathMeanSquare (m:=m) T) atTop (𝓝 0) := by
  have h := ((path_second_tendsto T hT hd).sub
    ((path_mean_tendsto T hT hd).const_mul (2*(1/(d : ℝ))))).add_const ((1/(d : ℝ))^2)
  have hz : (1/(d : ℝ))^2-2*(1/(d : ℝ))*(1/(d : ℝ))+(1/(d : ℝ))^2=0 := by ring
  rw [hz] at h
  apply h.congr'
  filter_upwards [actual_positive T hT hd] with m hm
  exact (centered_identity _ _ _ hm.2).symm

end
end WeightedMotif
