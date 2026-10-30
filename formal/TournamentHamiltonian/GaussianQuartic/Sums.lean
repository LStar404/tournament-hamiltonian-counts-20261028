module

public import TournamentHamiltonian.GaussianQuartic.Edges

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem pairMoment_algebra (i j k l : ι) (hij : i ≠ j) :
    pairMoment i j k l =
      144 - 144 * delta k l +
        312 * (delta i k + delta i l + delta j k + delta j l) -
        624 * (delta i k * delta k l + delta j k * delta k l) +
        912 * (delta i k * delta j l + delta i l * delta j k) := by
  by_cases hkl : k = l
  · subst l
    by_cases hik : i = k
    · subst k; norm_num [pairMoment, delta, hij, Ne.symm hij]
    · by_cases hjk : j = k
      · subst k; norm_num [pairMoment, delta, hij, Ne.symm hij]
      · simp [pairMoment, delta, hik, hjk]
  · simp [pairMoment, hij, hkl, delta]

theorem pairMoment_row_sum (i j : ι) (hij : i ≠ j) :
    (∑ k, ∑ l, pairMoment i j k l) =
      144 * (Fintype.card ι : ℝ) ^ 2 + 1104 * Fintype.card ι + 576 := by
  simp_rw [pairMoment_algebra i j _ _ hij]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, delta, mul_ite]
  ring

def orderedSum (z : ι → ℝ) : ℝ := ∑ i, ∑ j, edge4 i j z

theorem orderedSum_integrable : Integrable (orderedSum (ι := ι)) (gaussian ι) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => edge4_integrable i j))

theorem orderedSum_integral :
    (∫ z, orderedSum z ∂gaussian ι) = 12 * Fintype.card ι * ((Fintype.card ι : ℝ) - 1) := by
  simp only [orderedSum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => edge4_integrable i j))]
  simp_rw [integral_finsetSum _ (fun j _ => edge4_integrable _ j), edge4_integral]
  simp [Finset.sum_sub_distrib, mul_sub, delta]
  ring

omit [DecidableEq ι] in
theorem orderedSum_sq_expansion (z : ι → ℝ) :
    orderedSum z ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l, edge4 i j z * edge4 k l z := by
  simp only [orderedSum, pow_two]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem orderedSum_sq_integrable :
    Integrable (fun z : ι → ℝ => orderedSum z ^ 2) (gaussian ι) := by
  simp_rw [orderedSum_sq_expansion]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (edge4_pair_moments i j k l).1))))

theorem orderedSum_sq_integral :
    (∫ z : ι → ℝ, orderedSum z ^ 2 ∂gaussian ι) =
      (Fintype.card ι : ℝ) * (Fintype.card ι - 1) *
        (144 * (Fintype.card ι : ℝ) ^ 2 + 1104 * Fintype.card ι + 576) := by
  simp_rw [orderedSum_sq_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (edge4_pair_moments i j k l).1))))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (edge4_pair_moments _ j k l).1)))]
  simp_rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    (edge4_pair_moments _ _ k l).1))]
  simp_rw [integral_finsetSum _ (fun l _ => (edge4_pair_moments _ _ _ l).1)]
  simp_rw [(edge4_pair_moments _ _ _ _).2]
  have hrow (i j : ι) : (∑ k, ∑ l, pairMoment i j k l) =
      (1 - delta i j) *
        (144 * (Fintype.card ι : ℝ) ^ 2 + 1104 * Fintype.card ι + 576) := by
    by_cases hij : i = j
    · subst j; simp [pairMoment, delta]
    · simpa [delta, hij] using pairMoment_row_sum i j hij
  simp_rw [hrow]
  simp [Finset.sum_sub_distrib, mul_sub, sub_mul, delta]
  ring

end
end GaussianQuartic
