module

public import TournamentHamiltonian.NonregularDecay.Variance

@[expose] public section

set_option autoImplicit false

namespace NonregularDecay
open TournamentHamiltonian UniformBlowup Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem order_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun m : ℕ => d*m) atTop atTop := by
  apply tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hd) tendsto_id

/-- A positive cubic variance lower bound eventually exceeds the old uniform
high-variance cutoff. Its threshold depends only on d and V, not on any sample. -/
theorem cubic_eventually_highVariance {d : ℕ} (hd : 0 < d) {V : ℝ} (hV : 0 < V) :
    ∀ᶠ m : ℕ in atTop,
      16 * (d*m : ℝ)^2 * Real.log (d*m) ≤ (m : ℝ)^3 * V := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (order_tendsto hd)
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn
  filter_upwards [hl.eventually_le_const (show 0 < V / (16 * (d : ℝ)^3) by positivity),
    eventually_ge_atTop (1 : ℕ)] with m hl hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < d*m := mul_pos hdR hmR
  simp only [Function.comp_def, id_eq, Nat.cast_mul] at hl
  have hlog : Real.log (d*m) ≤ (d*m : ℝ) * (V / (16 * (d : ℝ)^3)) := by
    have h := (div_le_iff₀ hnR).mp hl
    simpa [mul_comm] using h
  calc
    _ ≤ 16 * (d*m : ℝ)^2 * ((d*m : ℝ) * (V / (16 * (d : ℝ)^3))) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (m : ℝ)^3 * V := by field_simp

theorem blowup_eventually_highVariance {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) :
    ∀ᶠ m : ℕ in atTop, ∀ ω : Sample d m, ∀ e : Arrangement d m,
      16 * (d*m : ℝ)^2 * Real.log (d*m) ≤ degreeVariance (blowup T ω e) := by
  filter_upwards [cubic_eventually_highVariance hd
    ((degreeVariance_pos_iff_nonregular T).mpr hT)] with m hm ω e
  exact hm.trans (degreeVariance_blowup_ge T ω e)

/-- Uniform actual path decay: one threshold works simultaneously for all
internal tournaments and all vertex relabellings. -/
theorem path_eventually_small {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ ω : Sample d m,
      (pathCount T ω : ℝ) / meanPaths (d*m) ≤ ε / (d*m) := by
  have hhigh := (order_tendsto hd).eventually
    (highVariance_pathCount_eventually_small hε)
  filter_upwards [blowup_eventually_highVariance hd T hT, hhigh] with m hV hbound ω
  rw [pathCount_eq_existing T ω (vertexEquiv d m)]
  simpa only [Nat.cast_mul] using hbound _ (by simpa only [Nat.cast_mul] using hV ω (vertexEquiv d m))

/-- In particular every possibly m-dependent choice of the internal blocks has
normalized path count tending to zero. -/
theorem path_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) (ω : ∀ m, Sample d m) :
    Tendsto (fun m => (pathCount T (ω m) : ℝ) / meanPaths (d*m)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m : ℕ => (1 : ℝ) / (d*m)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, Nat.cast_mul] using
      tendsto_one_div_atTop_nhds_zero_nat.comp (order_tendsto hd)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun m => by unfold meanPaths; positivity
  · filter_upwards [path_eventually_small hd T hT (by norm_num : (0 : ℝ) < 1)] with m hm
    exact hm (ω m)

end
end NonregularDecay
