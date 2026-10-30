module

public import TournamentHamiltonian.GaussianQuartic.Limit

@[expose] public section
set_option autoImplicit false
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory
noncomputable section

theorem mean_m1 : (∫ z, quartic 1 z ∂gaussian (Fin 1)) = (0/1 : ℝ) := by
  rw [quartic_mean 1 (by norm_num)]
  norm_num

theorem variance_m1 : variance (quartic 1) (gaussian (Fin 1)) = (0/1 : ℝ) := by
  rw [quartic_variance 1 (by norm_num)]
  norm_num

theorem mean_m2 : (∫ z, quartic 2 z ∂gaussian (Fin 2)) = (1/4 : ℝ) := by
  rw [quartic_mean 2 (by norm_num)]
  norm_num

theorem variance_m2 : variance (quartic 2) (gaussian (Fin 2)) = (2/3 : ℝ) := by
  rw [quartic_variance 2 (by norm_num)]
  norm_num

theorem mean_m3 : (∫ z, quartic 3 z ∂gaussian (Fin 3)) = (1/3 : ℝ) := by
  rw [quartic_mean 3 (by norm_num)]
  norm_num

theorem variance_m3 : variance (quartic 3) (gaussian (Fin 3)) = (5/9 : ℝ) := by
  rw [quartic_variance 3 (by norm_num)]
  norm_num

theorem mean_m4 : (∫ z, quartic 4 z ∂gaussian (Fin 4)) = (3/8 : ℝ) := by
  rw [quartic_mean 4 (by norm_num)]
  norm_num

theorem variance_m4 : variance (quartic 4) (gaussian (Fin 4)) = (29/64 : ℝ) := by
  rw [quartic_variance 4 (by norm_num)]
  norm_num

theorem mean_m5 : (∫ z, quartic 5 z ∂gaussian (Fin 5)) = (2/5 : ℝ) := by
  rw [quartic_mean 5 (by norm_num)]
  norm_num

theorem variance_m5 : variance (quartic 5) (gaussian (Fin 5)) = (142/375 : ℝ) := by
  rw [quartic_variance 5 (by norm_num)]
  norm_num

theorem mean_m6 : (∫ z, quartic 6 z ∂gaussian (Fin 6)) = (5/12 : ℝ) := by
  rw [quartic_mean 6 (by norm_num)]
  norm_num

theorem variance_m6 : variance (quartic 6) (gaussian (Fin 6)) = (35/108 : ℝ) := by
  rw [quartic_variance 6 (by norm_num)]
  norm_num

end
end GaussianQuartic
