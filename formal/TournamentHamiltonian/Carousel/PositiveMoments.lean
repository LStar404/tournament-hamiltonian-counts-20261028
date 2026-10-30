module
public import TournamentHamiltonian.Carousel.CotMoments
public import TournamentHamiltonian.Carousel.ScalarCot

@[expose] public section
namespace TournamentHamiltonian
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Every positive paired moment of the actual transitive tournament is the
finite sum of the manuscript's explicit normalized positive cotangents. -/
theorem transitive_pairedMoments_eq_positiveCot (m p : ℕ) (hp : 0 < p) :
    ((pairedMasses (transitiveTournament (2*m+1))).map (fun x => x^p)).sum =
      ∑ j : Fin m, carouselPositiveFrequency m j ^ (2*p) := by
  rw [pairedMasses_pow_sum_eq_positive]
  have h := positiveSkewFrequencies_even_pow_sum (transitiveTournament (2*m+1)) p hp
  rw [transitive_skewFrequency_even_sum_cot, transitive_cot_even_sum_half m p hp] at h
  have hh := mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) h
  rw [← hh]
  simp only [carouselPositiveFrequency, div_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [← Finset.sum_div]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    Real.cot ((2*(j : ℝ)+1)*Real.pi / (2*(2*(m : ℝ)+1))) ^ (2*p)) m).symm

/-- The first moment is exactly the quantity canceled by the regular-block exponential. -/
theorem carouselPositiveFrequency_sum_sq (m : ℕ) :
    2 * (∑ j : Fin m, carouselPositiveFrequency m j ^ 2) = 1 - 1/(2*(m : ℝ)+1) := by
  have hh := transitive_pairedMoments_eq_positiveCot m 1 (by omega)
  simp only [pow_one, Nat.mul_one] at hh
  have hid (xs : List ℝ) : (xs.map (fun x => x)).sum = xs.sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]
  rw [hid] at hh
  rw [← hh, pairedMasses_sum _ (by omega)]
  push_cast
  field_simp

/-- Increasing the odd order strictly increases every positive paired moment.
The new last positive frequency makes strictness hold even for `m = 0`. -/
theorem transitive_pairedMoments_lt_succ (m p : ℕ) (hp : 0 < p) :
    ((pairedMasses (transitiveTournament (2*m+1))).map (fun x => x^p)).sum <
      ((pairedMasses (transitiveTournament (2*(m+1)+1))).map (fun x => x^p)).sum := by
  rw [transitive_pairedMoments_eq_positiveCot m p hp,
    transitive_pairedMoments_eq_positiveCot (m+1) p hp, Fin.sum_univ_castSucc]
  have hs : (∑ j : Fin m, carouselPositiveFrequency m j ^ (2*p)) ≤
      ∑ j : Fin m, carouselPositiveFrequency (m+1) j.castSucc ^ (2*p) := by
    apply Finset.sum_le_sum
    intro j _
    have h := carouselPositiveFrequency_strictMono (show m < m+1 by omega) j
    have heq : j.castLT (j.isLt.trans (show m < m+1 by omega)) = j.castSucc := Fin.ext rfl
    rw [heq] at h
    exact pow_le_pow_left₀ (carouselPositiveFrequency_pos m j).le h.le _
  exact hs.trans_lt (lt_add_of_pos_right _
    (pow_pos (carouselPositiveFrequency_pos (m+1) (Fin.last m)) _))

end TournamentHamiltonian
