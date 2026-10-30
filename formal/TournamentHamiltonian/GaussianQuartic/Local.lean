module

public import TournamentHamiltonian.GaussianQuartic.Base

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory TournamentHamiltonian
open scoped BigOperators
noncomputable section

def fourthCoeff : Fin 5 → ℝ := ![1, -4, 6, -4, 1]
def fourthPower : Fin 5 → Fin 2 → ℕ := ![![4, 0], ![3, 1], ![2, 2], ![1, 3], ![0, 4]]
theorem fourth_expansion (z : Fin 2 → ℝ) :
    (z 0 - z 1) ^ 4 = polynomial fourthCoeff fourthPower z := by
  simp [polynomial, fourthCoeff, fourthPower, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem local_fourth_integrable :
    Integrable (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 4) (gaussian (Fin 2)) := by
  simp_rw [fourth_expansion]
  exact polynomial_integrable _ _

theorem local_fourth_integral :
    (∫ z : Fin 2 → ℝ, (z 0 - z 1) ^ 4 ∂gaussian (Fin 2)) = 12 := by
  simp_rw [fourth_expansion]
  rw [polynomial_integral]
  norm_num [fourthCoeff, fourthPower, Fin.sum_univ_succ, Fin.prod_univ_succ]

def eighthCoeff : Fin 9 → ℝ := ![1, -8, 28, -56, 70, -56, 28, -8, 1]
def eighthPower : Fin 9 → Fin 2 → ℕ := ![![8, 0], ![7, 1], ![6, 2], ![5, 3], ![4, 4], ![3, 5], ![2, 6], ![1, 7], ![0, 8]]
theorem eighth_expansion (z : Fin 2 → ℝ) :
    (z 0 - z 1) ^ 8 = polynomial eighthCoeff eighthPower z := by
  simp [polynomial, eighthCoeff, eighthPower, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem local_eighth_integrable :
    Integrable (fun z : Fin 2 → ℝ => (z 0 - z 1) ^ 8) (gaussian (Fin 2)) := by
  simp_rw [eighth_expansion]
  exact polynomial_integrable _ _

theorem local_eighth_integral :
    (∫ z : Fin 2 → ℝ, (z 0 - z 1) ^ 8 ∂gaussian (Fin 2)) = 1680 := by
  simp_rw [eighth_expansion]
  rw [polynomial_integral]
  norm_num [eighthCoeff, eighthPower, Fin.sum_univ_succ, Fin.prod_univ_succ]

def sharedCoeff : Fin 25 → ℝ := ![1, -4, -4, 6, 16, 6, -4, -24, -24, -4, 1, 16, 36, 16, 1, -4, -24, -24, -4, 6, 16, 6, -4, -4, 1]
def sharedPower : Fin 25 → Fin 3 → ℕ := ![![8, 0, 0], ![7, 1, 0], ![7, 0, 1], ![6, 2, 0], ![6, 1, 1], ![6, 0, 2], ![5, 3, 0], ![5, 2, 1], ![5, 1, 2], ![5, 0, 3], ![4, 4, 0], ![4, 3, 1], ![4, 2, 2], ![4, 1, 3], ![4, 0, 4], ![3, 4, 1], ![3, 3, 2], ![3, 2, 3], ![3, 1, 4], ![2, 4, 2], ![2, 3, 3], ![2, 2, 4], ![1, 4, 3], ![1, 3, 4], ![0, 4, 4]]
theorem shared_expansion (z : Fin 3 → ℝ) :
    (z 0 - z 1) ^ 4 * (z 0 - z 2) ^ 4 = polynomial sharedCoeff sharedPower z := by
  simp [polynomial, sharedCoeff, sharedPower, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem local_shared_integrable :
    Integrable (fun z : Fin 3 → ℝ => (z 0 - z 1) ^ 4 * (z 0 - z 2) ^ 4) (gaussian (Fin 3)) := by
  simp_rw [shared_expansion]
  exact polynomial_integrable _ _

theorem local_shared_integral :
    (∫ z : Fin 3 → ℝ, (z 0 - z 1) ^ 4 * (z 0 - z 2) ^ 4 ∂gaussian (Fin 3)) = 456 := by
  simp_rw [shared_expansion]
  rw [polynomial_integral]
  norm_num [sharedCoeff, sharedPower, Fin.sum_univ_succ, Fin.prod_univ_succ]

def disjointCoeff : Fin 25 → ℝ := ![1, -4, 6, -4, 1, -4, 16, -24, 16, -4, 6, -24, 36, -24, 6, -4, 16, -24, 16, -4, 1, -4, 6, -4, 1]
def disjointPower : Fin 25 → Fin 4 → ℕ := ![![4, 0, 4, 0], ![4, 0, 3, 1], ![4, 0, 2, 2], ![4, 0, 1, 3], ![4, 0, 0, 4], ![3, 1, 4, 0], ![3, 1, 3, 1], ![3, 1, 2, 2], ![3, 1, 1, 3], ![3, 1, 0, 4], ![2, 2, 4, 0], ![2, 2, 3, 1], ![2, 2, 2, 2], ![2, 2, 1, 3], ![2, 2, 0, 4], ![1, 3, 4, 0], ![1, 3, 3, 1], ![1, 3, 2, 2], ![1, 3, 1, 3], ![1, 3, 0, 4], ![0, 4, 4, 0], ![0, 4, 3, 1], ![0, 4, 2, 2], ![0, 4, 1, 3], ![0, 4, 0, 4]]
theorem disjoint_expansion (z : Fin 4 → ℝ) :
    (z 0 - z 1) ^ 4 * (z 2 - z 3) ^ 4 = polynomial disjointCoeff disjointPower z := by
  simp [polynomial, disjointCoeff, disjointPower, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem local_disjoint_integrable :
    Integrable (fun z : Fin 4 → ℝ => (z 0 - z 1) ^ 4 * (z 2 - z 3) ^ 4) (gaussian (Fin 4)) := by
  simp_rw [disjoint_expansion]
  exact polynomial_integrable _ _

theorem local_disjoint_integral :
    (∫ z : Fin 4 → ℝ, (z 0 - z 1) ^ 4 * (z 2 - z 3) ^ 4 ∂gaussian (Fin 4)) = 144 := by
  simp_rw [disjoint_expansion]
  rw [polynomial_integral]
  norm_num [disjointCoeff, disjointPower, Fin.sum_univ_succ, Fin.prod_univ_succ]

end
end GaussianQuartic
