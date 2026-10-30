module

public import TournamentHamiltonian.GaussianQuartic.Local

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι]

def edge4 (i j : ι) (z : ι → ℝ) : ℝ := (z i - z j) ^ 4

omit [Fintype ι] in
@[simp] theorem edge4_self (i : ι) (z : ι → ℝ) : edge4 i i z = 0 := by simp [edge4]
omit [Fintype ι] in
theorem edge4_symm (i j : ι) : edge4 i j = edge4 j i := by funext z; unfold edge4; ring

theorem edge4_moments (i j : ι) (hij : i ≠ j) :
    Integrable (edge4 i j) (gaussian ι) ∧ (∫ z, edge4 i j z ∂gaussian ι) = 12 := by
  let f : Fin 2 → ι := ![i,j]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  constructor
  · change Integrable (fun z : ι → ℝ => (z i - z j) ^ 4) (gaussian ι)
    simpa [Function.comp_def, f] using
      (restrict_preserving f hf).integrable_comp_of_integrable local_fourth_integrable
  · have h := integral_restrict f hf (fun z => (z 0 - z 1) ^ 4) (by fun_prop)
    simpa [edge4, f, local_fourth_integral] using h

theorem edge4_same_moments (i j : ι) (hij : i ≠ j) :
    Integrable (fun z => edge4 i j z * edge4 i j z) (gaussian ι) ∧
      (∫ z, edge4 i j z * edge4 i j z ∂gaussian ι) = 1680 := by
  let f : Fin 2 → ι := ![i,j]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have heq : (fun z => edge4 i j z * edge4 i j z) =
      (fun z : ι → ℝ => (z i - z j) ^ 8) := by funext z; unfold edge4; ring
  rw [heq]
  constructor
  · simpa [Function.comp_def, f] using
      (restrict_preserving f hf).integrable_comp_of_integrable local_eighth_integrable
  · have h := integral_restrict f hf (fun z => (z 0 - z 1) ^ 8) (by fun_prop)
    simpa [f, local_eighth_integral] using h

theorem edge4_shared_moments (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Integrable (fun z => edge4 i j z * edge4 i k z) (gaussian ι) ∧
      (∫ z, edge4 i j z * edge4 i k z ∂gaussian ι) = 456 := by
  let f : Fin 3 → ι := ![i,j,k]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  constructor
  · simpa [edge4, Function.comp_def, f] using
      (restrict_preserving f hf).integrable_comp_of_integrable local_shared_integrable
  · have h := integral_restrict f hf (fun z => (z 0 - z 1) ^ 4 * (z 0 - z 2) ^ 4)
      (by fun_prop)
    simpa [edge4, f, local_shared_integral] using h

theorem edge4_disjoint_moments (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Integrable (fun z => edge4 i j z * edge4 k l z) (gaussian ι) ∧
      (∫ z, edge4 i j z * edge4 k l z ∂gaussian ι) = 144 := by
  let f : Fin 4 → ι := ![i,j,k,l]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  constructor
  · simpa [edge4, Function.comp_def, f] using
      (restrict_preserving f hf).integrable_comp_of_integrable local_disjoint_integrable
  · have h := integral_restrict f hf (fun z => (z 0 - z 1) ^ 4 * (z 2 - z 3) ^ 4)
      (by fun_prop)
    simpa [edge4, f, local_disjoint_integral] using h

variable [DecidableEq ι]

def delta (i j : ι) : ℝ := if i = j then 1 else 0

def pairMoment (i j k l : ι) : ℝ :=
  if i = j ∨ k = l then 0 else
    144 + 312 * (delta i k + delta i l + delta j k + delta j l) +
      912 * (delta i k * delta j l + delta i l * delta j k)

theorem edge4_pair_moments (i j k l : ι) :
    Integrable (fun z => edge4 i j z * edge4 k l z) (gaussian ι) ∧
      (∫ z, edge4 i j z * edge4 k l z ∂gaussian ι) = pairMoment i j k l := by
  by_cases hij : i = j
  · subst j
    simp [pairMoment]
  by_cases hkl : k = l
  · subst l
    simp [pairMoment]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      convert edge4_same_moments i j hij using 1; norm_num [pairMoment, delta, hij, Ne.symm hij]
    · convert edge4_shared_moments i j l hij hkl hjl using 1; norm_num [pairMoment, delta, hij, Ne.symm hij, hkl, Ne.symm hkl, hjl, Ne.symm hjl]
  by_cases hjk : j = k
  · subst k
    by_cases hil : i = l
    · subst l
      rw [edge4_symm j i]
      convert edge4_same_moments i j hij using 1; norm_num [pairMoment, delta, hij, Ne.symm hij]
    · rw [edge4_symm i j]
      convert edge4_shared_moments j i l (Ne.symm hij) hkl hil using 1; norm_num [pairMoment, delta, hij, Ne.symm hij, hkl, Ne.symm hkl, hil, Ne.symm hil]
  by_cases hil : i = l
  · subst l
    rw [edge4_symm k i]
    convert edge4_shared_moments i j k hij hik hjk using 1; norm_num [pairMoment, delta, hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
  by_cases hjl : j = l
  · subst l
    rw [edge4_symm i j, edge4_symm k j]
    convert edge4_shared_moments j i k (Ne.symm hij) hjk hik using 1; norm_num [pairMoment, delta, hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
  simpa [pairMoment, delta, hij, hkl, hik, hil, hjk, hjl] using
    edge4_disjoint_moments i j k l hij hik hil hjk hjl hkl

theorem edge4_integrable (i j : ι) : Integrable (edge4 i j) (gaussian ι) := by
  by_cases h : i = j
  · subst j
    change Integrable (fun z : ι → ℝ => (z i - z i) ^ 4) (gaussian ι)
    simp
  · exact (edge4_moments i j h).1

theorem edge4_integral (i j : ι) :
    (∫ z, edge4 i j z ∂gaussian ι) = 12 * (1 - delta i j) := by
  by_cases h : i = j
  · subst j; simp [delta]
  · simpa [delta, h] using (edge4_moments i j h).2

end
end GaussianQuartic
