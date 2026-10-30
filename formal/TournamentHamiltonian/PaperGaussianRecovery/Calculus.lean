module

public import TournamentHamiltonian.PaperGaussianRecovery.Spectrum

@[expose] public section

set_option autoImplicit false
namespace PaperGaussianRecovery
open Filter
open scoped BigOperators Topology
noncomputable section
variable {ι : Type*} [Fintype ι]

def spectralGaussian (s : ι → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(1/2:ℝ)*∑ i,Real.log (1-t^2*s i))
def spectralU (s : ι → ℝ) (t : ℝ) : ℝ := ∑ i,t*s i/(1-t^2*s i)
def spectralV (s : ι → ℝ) (t : ℝ) : ℝ := ∑ i,s i*(1+t^2*s i)/(1-t^2*s i)^2

theorem hasDerivAt_spectralGaussian (s : ι → ℝ) (t : ℝ) (hp : ∀ i,0<1-t^2*s i) :
    HasDerivAt (spectralGaussian s) (spectralGaussian s t * spectralU s t) t := by
  have hi (i : ι) : HasDerivAt (fun x : ℝ => Real.log (1-x^2*s i))
      (-(2*t*s i)/(1-t^2*s i)) t := by
    convert ((hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).pow 2).mul_const (s i))).log (hp i).ne' using 1 <;> simp [mul_comm]
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hi i)
  have he := (hs.const_mul (-(1/2:ℝ))).exp
  convert he using 1
  · rfl
  · unfold spectralGaussian spectralU
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem hasDerivAt_spectralU (s : ι → ℝ) (t : ℝ) (hp : ∀ i,0<1-t^2*s i) :
    HasDerivAt (spectralU s) (spectralV s t) t := by
  have hi (i : ι) : HasDerivAt (fun x : ℝ => x*s i/(1-x^2*s i))
      (s i*(1+t^2*s i)/(1-t^2*s i)^2) t := by
    convert ((hasDerivAt_id t).mul_const (s i)).div
      ((hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).pow 2).mul_const (s i)))
      (hp i).ne' using 1
    · funext x
      dsimp
    · dsimp
      ring
  exact HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hi i)

theorem spectral_gap_eventually (s : ι → ℝ) (t : ℝ) (hp : ∀ i,0<1-t^2*s i) :
    ∀ᶠ x in 𝓝 t, ∀ i,0<1-x^2*s i := by
  apply Filter.eventually_all.mpr
  intro i
  exact (continuous_const.sub ((continuous_id.pow 2).mul continuous_const)).continuousAt.eventually
    (lt_mem_nhds (hp i))

theorem spectralGaussian_second_derivative (s : ι → ℝ) (t : ℝ) (hp : ∀ i,0<1-t^2*s i) :
    iteratedDeriv 2 (spectralGaussian s) t =
      spectralGaussian s t * ((spectralU s t)^2+spectralV s t) := by
  have he : deriv (spectralGaussian s) =ᶠ[𝓝 t]
      (fun x => spectralGaussian s x * spectralU s x) := by
    filter_upwards [spectral_gap_eventually s t hp] with x hx
    exact (hasDerivAt_spectralGaussian s x hx).deriv
  have hd := (hasDerivAt_spectralGaussian s t hp).mul (hasDerivAt_spectralU s t hp)
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [he.deriv_eq]
  change deriv (spectralGaussian s * spectralU s) t = _
  rw [hd.deriv]
  ring

end
end PaperGaussianRecovery
