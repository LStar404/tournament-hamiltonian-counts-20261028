module
public import TournamentHamiltonian.TransitiveCotSpectrum
public import TournamentHamiltonian.SpectralPowerMoments
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section
namespace TournamentHamiltonian
open scoped Classical

/-- Full multiset identity: no eigenvalue multiplicities are dropped. -/
theorem transitive_skewFrequency_multiset_cot (n : ℕ) :
    Finset.univ.val.map (skewFrequency (transitiveTournament n)) =
      Finset.univ.val.map (fun j => -Real.cot (transitiveCotAngle n j)) := by
  have hc : (skewHermitian (transitiveTournament n)).charpoly =
      (Matrix.diagonal (fun j : Fin n => -(Real.cot (transitiveCotAngle n j) : ℂ))).charpoly := by
    rw [← transitiveHermitian_cotBasis_toMatrix, LinearMap.charpoly_toMatrix,
      Matrix.charpoly_toLin']
  have hr := (skewHermitian_isHermitian (transitiveTournament n)).roots_charpoly_eq_eigenvalues
  change (skewHermitian (transitiveTournament n)).charpoly.roots =
    Finset.univ.val.map (fun i => (skewFrequency (transitiveTournament n) i : ℂ)) at hr
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod] at hr
  · have hh := congrArg (Multiset.map Complex.re) hr
    simpa only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map, skewFrequency,
      Function.comp_def, Complex.neg_re, Complex.ofReal_re] using hh.symm
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)

/-- Every even power sum of the real frequencies equals the explicit cotangent sum. -/
theorem transitive_skewFrequency_even_sum_cot (n p : ℕ) :
    (∑ i, skewFrequency (transitiveTournament n) i ^ (2*p)) =
      ∑ i : Fin n, Real.cot (transitiveCotAngle n i) ^ (2*p) := by
  have h := congrArg (fun M : Multiset ℝ => (M.map (fun x => x^(2*p))).sum)
    (transitive_skewFrequency_multiset_cot n)
  simpa only [Multiset.map_map, Function.comp_def, Finset.sum_map_val,
    pow_mul, neg_sq] using h

/-- Split an odd symmetric finite sequence into its two equal halves. -/
theorem odd_symmetric_sum (f : ℕ → ℝ) (m : ℕ)
    (hmid : f m = 0) (hsym : ∀ j < m, f (m + (j + 1)) = f (m - 1 - j)) :
    (∑ j ∈ Finset.range (2*m+1), f j) = 2 * ∑ j ∈ Finset.range m, f j := by
  rw [show 2*m+1 = m+(m+1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ']
  simp only [hmid, add_zero]
  have hhalf : (∑ j ∈ Finset.range m, f (m + (j+1))) = ∑ j ∈ Finset.range m, f j := by
    calc
      _ = ∑ j ∈ Finset.range m, f (m-1-j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsym j (Finset.mem_range.mp hj)
      _ = _ := Finset.sum_range_reflect f m
  rw [hhalf]
  ring

/-- Symmetry about the zero middle frequency gives the complete positive half. -/
theorem transitive_cot_even_sum_half (m p : ℕ) (hp : 0 < p) :
    (∑ i : Fin (2*m+1), Real.cot (transitiveCotAngle (2*m+1) i) ^ (2*p)) =
      2 * ∑ j ∈ Finset.range m,
        Real.cot ((2*(j : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1))) ^ (2*p) := by
  simp only [transitiveCotAngle, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    Real.cot ((2*(j : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1))) ^ (2*p))]
  apply odd_symmetric_sum
  · have ha : (2*(m : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1)) = Real.pi/2 := by field_simp
    rw [ha, Real.cot_eq_cos_div_sin, Real.cos_pi_div_two, zero_div,
      zero_pow (by omega : 2*p ≠ 0)]
  · intro j hj
    have hcast : ((m-1-j : ℕ) : ℝ) = (m : ℝ)-1-j := by
      rw [Nat.cast_sub (by omega : j ≤ m-1), Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have ha : (2*((m+(j+1) : ℕ) : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1)) =
        Real.pi - (2*((m-1-j : ℕ) : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1)) := by
      rw [hcast]
      push_cast
      field_simp
      ring
    rw [ha, Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div,
      pow_mul, neg_sq, ← Real.cot_eq_cos_div_sin, ← pow_mul]

end TournamentHamiltonian
