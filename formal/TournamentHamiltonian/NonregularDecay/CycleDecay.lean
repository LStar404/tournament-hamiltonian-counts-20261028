module

public import TournamentHamiltonian.NonregularDecay.PathDecay
public import TournamentHamiltonian.NonregularDecay.CycleBound

@[expose] public section

set_option autoImplicit false

namespace NonregularDecay
open TournamentHamiltonian UniformBlowup Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A common scalar majorant, tending to zero; this is not an abstract cycle count. -/
def cycleMajorant (n : ℕ) : ℝ :=
  Real.exp 7 * ((n : ℝ) * Real.sqrt ((n : ℝ)+1) * (n : ℝ)^(-(13/8 : ℝ)))

theorem cycleMajorant_tendsto_zero : Tendsto cycleMajorant atTop (𝓝 0) := by
  have h := (scaled_highVariance_prefactor_tendsto_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (Real.exp 7)
  simp only [mul_zero] at h
  exact h

theorem permanent_normalized_le_cycleMajorant {n : ℕ} (T : Tournament n)
    (hn : 3 ≤ n) (hV : 16 * (n : ℝ)^2 * Real.log n ≤ degreeVariance T) :
    (adjacency T).permanent / meanCycles n ≤ cycleMajorant n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hvar : (13/8 : ℝ) * Real.log n ≤ degreeVariance T / (8*(n : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hs : 0 ≤ (n : ℝ)^2 * Real.log n := mul_nonneg (sq_nonneg _) hL
    nlinarith
  have hexp : Real.exp (-degreeVariance T / (8*(n : ℝ)^2)) ≤
      (n : ℝ)^(-(13/8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have h := (adjacency_permanent_le_stirling_variance T hn).trans
    (mul_le_mul_of_nonneg_left hexp (by positivity))
  apply (div_le_iff₀ (meanCycles_pos n)).mpr
  calc
    _ ≤ _ := h
    _ = cycleMajorant n * meanCycles n := by
      rw [show Real.exp 7 * Real.sqrt ((n : ℝ)+1) * (n.factorial : ℝ) / (2 : ℝ)^n =
        Real.exp 7 * Real.sqrt ((n : ℝ)+1) * ((n.factorial : ℝ) / (2 : ℝ)^n) by ring]
      rw [factorial_normalization_eq n (by omega), cycleMajorant]
      ring

/-- One scalar majorant bounds every actual blowup sample beyond the same threshold. -/
theorem cycle_eventually_le_majorant {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) :
    ∀ᶠ m : ℕ in atTop, ∀ ω : Sample d m,
      (cycleCount T ω : ℝ) / meanCycles (d*m) ≤ cycleMajorant (d*m) := by
  filter_upwards [blowup_eventually_highVariance hd T hT,
    (order_tendsto hd).eventually (eventually_ge_atTop (3 : ℕ))] with m hV hn ω
  apply (div_le_div_of_nonneg_right (cycleCount_le_permanent T ω (vertexEquiv d m))
    (meanCycles_pos _).le).trans
  exact permanent_normalized_le_cycleMajorant _ hn (by simpa only [Nat.cast_mul] using hV ω _)

theorem cycle_tendsto_zero {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) (ω : ∀ m, Sample d m) :
    Tendsto (fun m => (cycleCount T (ω m) : ℝ) / meanCycles (d*m)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (cycleMajorant_tendsto_zero.comp (order_tendsto hd))
  · exact Filter.Eventually.of_forall fun m => div_nonneg (by positivity) (meanCycles_pos _).le
  · filter_upwards [cycle_eventually_le_majorant hd T hT] with m hm
    exact hm (ω m)

end
end NonregularDecay
