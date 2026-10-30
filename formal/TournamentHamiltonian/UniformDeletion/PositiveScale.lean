module

public import TournamentHamiltonian.FixedDeletion.Estimates
public import TournamentHamiltonian.UniformFinal.UniformDenseCountLimit

@[expose] public section

set_option autoImplicit false
namespace UniformDeletion
open TournamentHamiltonian UniformDenseLimit Filter
open scoped BigOperators Topology
noncomputable section

/-- A lower bound on a genuinely scaled count and an upper bound on the scaled
permanent give a nonzero lower bound on their quotient. -/
theorem scaled_quotient_lower (s p x L P : ℝ) (hs : 0 < s) (hp : 0 < p)
    (hL : 0 < L) (hP : 0 < P) (hx : L ≤ s*x) (hb : s*p ≤ P) : L/P ≤ x/p := by
  have hx0 : 0 < x := (mul_pos_iff_of_pos_left hs).mp (hL.trans_le hx)
  apply (div_le_div_iff₀ hP hp).mpr
  calc
    L*p ≤ (s*x)*p := mul_le_mul_of_nonneg_right hx hp.le
    _ = x*(s*p) := by ring
    _ ≤ x*P := mul_le_mul_of_nonneg_left hb hx0.le

/-- Actual full uniform cycle/path counts and their original-permanent ratios
are eventually positive, with a common lower constant depending only on T,d. -/
theorem actual_full_scales_positive {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      0 < (density (m := m) T).permanent ∧
      0 < WeightedCycle.cyc (density (m := m) T) ∧
      0 < WeightedCycle.path (density (m := m) T) ∧
      c ≤ (d*m : ℕ)*WeightedCycle.cyc (density (m := m) T)/(density (m := m) T).permanent ∧
      c ≤ WeightedCycle.path (density (m := m) T)/((d*m : ℕ)*(density (m := m) T).permanent) := by
  let L := Real.exp 1*spectralRatio T
  let P := denseScaledPermanentBound+1
  have hL : 0 < L := mul_pos (Real.exp_pos _) (spectralRatio_bounds T hd).1
  have hP : 0 < P := by dsimp [P]; linarith [denseScaleBounds_nonneg.2.2]
  refine ⟨(L/2)/P, by positivity, ?_⟩
  have hc := Filter.Tendsto.eventually_const_lt (by dsimp [L]; linarith : L/2 < L)
    (scaled_cycle_tendsto T hT hd)
  have hh := Filter.Tendsto.eventually_const_lt (by linarith : L/2 < L)
    (scaled_path_tendsto T hT hd)
  obtain ⟨N,hN⟩ := exists_nat_ge (2*denseFullPermanentConstant)
  filter_upwards [hc,hh,UniformBlockMatrix.eventually_order_ge d (max 20 N) hd] with m hcm hhm hnm
  let n := d*m
  let D := density (m := m) T
  let s : ℝ := (n : ℝ)^n/(n.factorial : ℝ)
  have hn20 : 20 ≤ n := (le_max_left _ _).trans hnm
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := by dsimp [s]; positivity
  have hD : DenseStochastic D := UniformBlockMatrix.uniform_densityFin_denseStochastic T hT hn20
  have hlarge : 2*denseFullPermanentConstant ≤ (n : ℝ) :=
    hN.trans (by exact_mod_cast ((le_max_right _ _).trans hnm))
  have hp : 0 < D.permanent := (by positivity : (0 : ℝ) < (n.factorial : ℝ)/(2*(n : ℝ)^n)).trans_le
    (hD.permanent_lower hn hlarge)
  have hb : s*D.permanent ≤ P := by
    have h := (le_abs_self (s*D.permanent)).trans (hD.scaled_permanent_uniform_bound hn)
    dsimp [P]; linarith
  have hc' : L/2 ≤ s*((n : ℝ)*WeightedCycle.cyc D) := hcm.le
  have hh' : L/2 ≤ s*(WeightedCycle.path D/(n : ℝ)) := hhm.le
  have hcl := scaled_quotient_lower s D.permanent _ (L/2) P hs hp (by positivity) hP hc' hb
  have hhl := scaled_quotient_lower s D.permanent _ (L/2) P hs hp (by positivity) hP hh' hb
  have hcp : 0 < WeightedCycle.cyc D := by
    have hx : 0 < (n : ℝ)*WeightedCycle.cyc D :=
      (mul_pos_iff_of_pos_left hs).mp ((by positivity : (0 : ℝ) < L/2).trans_le hc')
    exact (mul_pos_iff_of_pos_left hnR).mp hx
  have hhp : 0 < WeightedCycle.path D := by
    have hx : 0 < WeightedCycle.path D/(n : ℝ) :=
      (mul_pos_iff_of_pos_left hs).mp ((by positivity : (0 : ℝ) < L/2).trans_le hh')
    exact (div_pos_iff_of_pos_right hnR).mp hx
  exact ⟨hp,hcp,hhp,hcl,by simpa only [div_div] using hhl⟩

end
end UniformDeletion
