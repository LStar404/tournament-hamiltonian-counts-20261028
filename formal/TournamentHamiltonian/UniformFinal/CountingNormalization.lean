module

public import TournamentHamiltonian.UniformFinal.ScalarLimits
public import TournamentHamiltonian.WeightedCycle.UniformBridge
public import TournamentHamiltonian.WeightedCycle.PathIntegration
public import TournamentHamiltonian.BlockMatrix.UniformDenseBridge
public import TournamentHamiltonian.BlockRatio.UniformLimit

@[expose] public section

namespace UniformFinalScalars
open TournamentHamiltonian WeightedCycle
noncomputable section
open scoped Classical

/-- The manuscript's uniform one-block expected cycle count. -/
def nu (n : ℕ) : ℝ := ((n-1).factorial : ℝ) / 2^n
/-- The manuscript's uniform one-block expected path count. -/
def mu (n : ℕ) : ℝ := (n.factorial : ℝ) / 2^(n-1)

theorem mu_eq_one_block_avgPath (n : ℕ) (T : Tournament 1) :
    mu n = UniformBlowup.avgPath (m := n) T :=
  (UniformBlowup.avgPath_one_block n T).symm

theorem nu_eq_one_block_avgCycle (n : ℕ) (hn : 3 ≤ n) (T : Tournament 1) :
    nu n = UniformBlowup.avgCycle (m := n) T :=
  (UniformBlowup.avgCycle_one_block n hn T).symm

/-- Scalar restoration with the unrooted-cycle factorial, including its
necessary N multiplier in the normalized stochastic count. -/
theorem cycle_scalar_restoration (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    x / nu n = cyclePrefactor n *
      ((n : ℝ)^n / (n.factorial : ℝ) * (n : ℝ) *
        ((2 / ((n : ℝ)-1))^n * x)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf : (n.factorial : ℝ) = (n : ℝ) * ((n-1).factorial : ℝ) := by
    have he : n-1+1=n := by omega
    exact_mod_cast (show n.factorial = n*(n-1).factorial by rw [← he, Nat.factorial_succ]; simp)
  unfold nu cyclePrefactor normalizationBase
  rw [hf, div_pow, div_pow]
  field_simp

/-- Path restoration has exponent N−1 and divides the normalized count by N. -/
theorem path_scalar_restoration (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    x / mu n = pathPrefactor n *
      ((n : ℝ)^n / (n.factorial : ℝ) *
        ((2 / ((n : ℝ)-1))^(n-1) * x) / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hp : (n : ℝ)^n = (n : ℝ)^(n-1)*(n : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  unfold mu pathPrefactor normalizationBase
  rw [hp, div_pow, div_pow]
  field_simp

/-- Actual weighted cycle normalization, no permanent asymptotic used. -/
theorem cyc_density_restoration {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hn : 2 ≤ Fintype.card α) :
    cyc A / nu (Fintype.card α) = cyclePrefactor (Fintype.card α) *
      ((Fintype.card α : ℝ)^(Fintype.card α) / ((Fintype.card α).factorial : ℝ) *
        (Fintype.card α : ℝ) * cyc ((2 / ((Fintype.card α : ℝ)-1)) • A)) := by
  rw [cyc_smul]
  exact cycle_scalar_restoration _ hn _

theorem path_density_restoration {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hn : 2 ≤ Fintype.card α) :
    path A / mu (Fintype.card α) = pathPrefactor (Fintype.card α) *
      ((Fintype.card α : ℝ)^(Fintype.card α) / ((Fintype.card α).factorial : ℝ) *
        path ((2 / ((Fintype.card α : ℝ)-1)) • A) / (Fintype.card α : ℝ)) := by
  rw [path_smul]
  exact path_scalar_restoration _ hn _

end
end UniformFinalScalars
