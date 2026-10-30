module

public import TournamentHamiltonian.PaperGaussianRecovery.Calculus

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PaperGaussianRecovery
open TournamentHamiltonian Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

theorem gramGaussian_eq_spectral (B : Matrix ι ι ℝ) (t : ℝ)
    (hp : ∀ i,0<1-t^2*gramEigenvalues B i) :
    gramGaussian (t • B) = spectralGaussian (gramEigenvalues B) t := by
  have hdet : 0<((1 : Matrix ι ι ℝ)-(t • B).transpose*(t • B)).det := by
    rw [det_gram_scale]
    exact Finset.prod_pos (fun i _ => hp i)
  have hpos : 0<gramGaussian (t • B) := by
    unfold gramGaussian
    exact inv_pos.mpr (Real.sqrt_pos.mpr hdet)
  rw [←Real.exp_log hpos, gramGaussian_log _ hdet, det_gram_scale,
    Real.log_prod (fun i _ => (hp i).ne')]
  rfl

theorem gramGaussian_second_derivative (B : Matrix ι ι ℝ) (t : ℝ)
    (hp : ∀ i,0<1-t^2*gramEigenvalues B i) :
    iteratedDeriv 2 (fun s : ℝ => gramGaussian (s • B)) t =
      gramGaussian (t • B)*((spectralU (gramEigenvalues B) t)^2+
        spectralV (gramEigenvalues B) t) := by
  have he : (fun s : ℝ => gramGaussian (s • B)) =ᶠ[𝓝 t]
      spectralGaussian (gramEigenvalues B) := by
    filter_upwards [spectral_gap_eventually (gramEigenvalues B) t hp] with x hx
    exact gramGaussian_eq_spectral B x hx
  rw [he.iteratedDeriv_eq 2, spectralGaussian_second_derivative _ _ hp,
    ←gramGaussian_eq_spectral B t hp]

def spectralA (s : ι → ℝ) (t : ℝ) : ℝ := ∑ i,t^2*s i/(1-t^2*s i)
def spectralB (s : ι → ℝ) (t : ℝ) : ℝ := ∑ i,t^2*s i*(1+t^2*s i)/(1-t^2*s i)^2

theorem spectralA_eq (s : ι → ℝ) (t : ℝ) : spectralA s t = t*spectralU s t := by
  unfold spectralA spectralU
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectralB_eq (s : ι → ℝ) (t : ℝ) : spectralB s t = t^2*spectralV s t := by
  unfold spectralB spectralV
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gramGaussian_factorial_second_derivative (B : Matrix ι ι ℝ) (t : ℝ)
    (hp : ∀ i,0<1-t^2*gramEigenvalues B i) :
    t^2*iteratedDeriv 2 (fun s : ℝ => gramGaussian (s • B)) t =
      gramGaussian (t • B)*((spectralA (gramEigenvalues B) t)^2+
        spectralB (gramEigenvalues B) t) := by
  rw [gramGaussian_second_derivative B t hp,spectralA_eq,spectralB_eq]
  ring

end
end PaperGaussianRecovery
