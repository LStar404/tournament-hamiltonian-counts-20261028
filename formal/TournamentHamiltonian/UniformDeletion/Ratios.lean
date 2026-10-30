module

public import TournamentHamiltonian.UniformDeletion.PositiveScale

@[expose] public section

set_option autoImplicit false
namespace UniformDeletion
open TournamentHamiltonian UniformDenseLimit FixedDeletion Filter
open scoped BigOperators Topology
noncomputable section

theorem relative_error_of_scaled (x y p c b : ℝ) (hy : 0 < y) (hp : 0 < p)
    (hc : 0 < c) (hb : 0 ≤ b) (hscale : c ≤ y/p) (he : |(x-y)/p| ≤ b) :
    |x/y-1| ≤ b/c := by
  have hid : x/y-1 = ((x-y)/p)/(y/p) := by field_simp
  rw [hid, abs_div, abs_of_pos (div_pos hy hp)]
  exact (div_le_div_of_nonneg_right he (div_pos hy hp).le).trans
    (div_le_div_of_nonneg_left hb hc hscale)

theorem rescale_relative_error (a q b : ℝ) (hq : 0 < q) (hql : 1/2 ≤ q)
    (hqu : q ≤ 1) (hb : 0 ≤ b) (he : |q*a-1| ≤ b) :
    |a-1| ≤ 2*b+2*(1-q) := by
  have hid : a-1 = ((q*a-1)+(1-q))/q := by field_simp; ring
  rw [hid, abs_div, abs_of_pos hq]
  calc
    _ ≤ (|q*a-1|+|1-q|)/q := div_le_div_of_nonneg_right (abs_add_le _ _) hq.le
    _ ≤ (b+(1-q))/q := div_le_div_of_nonneg_right
      (add_le_add he (le_of_eq (abs_of_nonneg (sub_nonneg.mpr hqu)))) hq.le
    _ ≤ _ := by
      apply (div_le_iff₀ hq).mpr
      nlinarith [mul_nonneg (show 0 ≤ q-1/2 by linarith) (show 0 ≤ b+1-q by linarith)]

theorem density_cycle_ratio_le {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) (hk : 2*U.card ≤ n) (c : ℝ) (hc : 0 < c)
    (hp : 0 < D.permanent) (hC : 0 < WeightedCycle.cyc D)
    (hlow : c ≤ (n : ℝ)*WeightedCycle.cyc D/D.permanent) :
    |WeightedCycle.cyc (densePrincipalMinor D U)/WeightedCycle.cyc D-1| ≤
      2*(budget U.card n/c)+2*((U.card : ℝ)/n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : U.card ≤ n := by omega
  have hM : (0 : ℝ) < (n-U.card : ℕ) := by exact_mod_cast (show 0 < n-U.card by omega)
  have hcast : ((n-U.card : ℕ) : ℝ) = (n : ℝ)-U.card := Nat.cast_sub hkn
  have hr := relative_error_of_scaled
    (((n-U.card : ℕ) : ℝ)*WeightedCycle.cyc (densePrincipalMinor D U))
    ((n : ℝ)*WeightedCycle.cyc D) D.permanent c (budget U.card n)
    (mul_pos hnR hC) hp hc (budget_nonneg _ _) hlow (cycle_deletion_le_budget hD hn hlarge U)
  let q : ℝ := ((n-U.card : ℕ) : ℝ)/n
  have hq : 0 < q := div_pos hM hnR
  have hql : 1/2 ≤ q := by
    apply (le_div_iff₀ hnR).mpr
    rw [hcast]
    have hh : 2*(U.card : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have hqu : q ≤ 1 := by
    apply (div_le_one hnR).mpr
    rw [hcast]
    linarith [Nat.cast_nonneg (α := ℝ) U.card]
  have hr' : |q*(WeightedCycle.cyc (densePrincipalMinor D U)/WeightedCycle.cyc D)-1| ≤ budget U.card n/c := by
    convert hr using 1
    dsimp [q]
    congr 1
    ring
  have h := rescale_relative_error _ q _ hq hql hqu (div_nonneg (budget_nonneg _ _) hc.le) hr'
  have heq : 1-q = (U.card : ℝ)/n := by
    dsimp [q]
    rw [hcast]
    field_simp
    ring
  simpa only [heq] using h

theorem density_path_ratio_le {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (n : ℝ))
    (U : Finset (Fin n)) (c : ℝ) (hc : 0 < c)
    (hp : 0 < D.permanent) (hH : 0 < WeightedCycle.path D)
    (hlow : c ≤ WeightedCycle.path D/((n : ℝ)*D.permanent)) :
    |WeightedCycle.path (densePrincipalMinor D U)/WeightedCycle.path D-1| ≤ budget U.card n/c := by
  exact relative_error_of_scaled _ _ _ _ _ hH (mul_pos (by exact_mod_cast hn) hp) hc
    (budget_nonneg _ _) hlow (path_deletion_le_budget hD hn hlarge U)

/-- Epsilon cutoff precedes every deleted set of the chosen fixed size. The
actual full Hamilton counts, not just the permanent, are proved positive. -/
theorem actual_density_deletion_ratios {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      0 < WeightedCycle.cyc (density (m := m) T) ∧
      0 < WeightedCycle.path (density (m := m) T) ∧
      ∀ U : Finset (Fin (d*m)), U.card = k →
        |WeightedCycle.cyc (densePrincipalMinor (density (m := m) T) U)/
            WeightedCycle.cyc (density (m := m) T)-1| < ε ∧
        |WeightedCycle.path (densePrincipalMinor (density (m := m) T) U)/
            WeightedCycle.path (density (m := m) T)-1| < ε := by
  intro ε hε
  obtain ⟨c,hc,hpos⟩ := actual_full_scales_positive T hT hd
  have hm : Tendsto (fun m : ℕ => d*m) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact UniformBlockMatrix.eventually_order_ge d b hd
  have hb : Tendsto (fun m : ℕ => budget k (d*m)/c) atTop (𝓝 0) := by
    simpa using ((budget_tendsto k).comp hm).div_const c
  have hk : Tendsto (fun m : ℕ => (k : ℝ)/(d*m : ℕ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hm).const_div_atTop _
  have he : Tendsto (fun m : ℕ => 2*(budget k (d*m)/c)+2*((k : ℝ)/(d*m : ℕ))) atTop (𝓝 0) := by
    simpa using (hb.const_mul 2).add (hk.const_mul 2)
  have hevent := Filter.Tendsto.eventually_lt_const hε he
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(denseFullPermanentConstant+denseScaledPermanentConstant+1))
  filter_upwards [hpos,hevent,UniformBlockMatrix.eventually_order_ge d (max 20 (max N (2*k))) hd]
    with m hpm hem hnm
  obtain ⟨hp,hC,hH,hcl,hhl⟩ := hpm
  have hn20 : 20 ≤ d*m := (le_max_left _ _).trans hnm
  have hn : 0 < d*m := by omega
  have hnm' : max N (2*k) ≤ d*m := (le_max_right _ _).trans hnm
  have hk2 : 2*k ≤ d*m := (le_max_right _ _).trans hnm'
  have hlarge : 4*(denseFullPermanentConstant+denseScaledPermanentConstant+1) ≤ (d*m : ℕ) :=
    hN.trans (by exact_mod_cast ((le_max_left _ _).trans hnm'))
  have hD := UniformBlockMatrix.uniform_densityFin_denseStochastic T hT hn20
  refine ⟨hC,hH,?_⟩
  intro U hU
  have hcu := density_cycle_ratio_le hD hn hlarge U (by simpa only [hU] using hk2) c hc hp hC hcl
  have hhu := density_path_ratio_le hD hn hlarge U c hc hp hH hhl
  rw [hU] at hcu hhu
  refine ⟨hcu.trans_lt hem, hhu.trans_lt ?_⟩
  have h0 := div_nonneg (budget_nonneg k (d*m)) hc.le
  have h1 : (0 : ℝ) ≤ (k : ℝ)/(d*m : ℕ) := by positivity
  linarith

end
end UniformDeletion
