module

public import TournamentHamiltonian.DenseGramScaling
public import TournamentHamiltonian.LowerDeletionFactorial
public import TournamentHamiltonian.SmallScoreLogBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace TournamentHamiltonian

/-- Second-order mass cancellation uses the actual retained mass N-2k+s,
not separate first-order estimates of its two normalizing factors. -/
theorem dense_minor_mass_log_scalar (N k s : ℝ) (hN : 0 < N) (hk : 0 ≤ k)
    (hsmall : k ≤ N/16) (hs0 : 0 ≤ s) (hs3 : s ≤ 3*k^2/N) :
    |(N-k) * Real.log (N*(N-2*k+s)/(N-k)^2)| ≤ 8*k^2/N := by
  have hM : 0 < N-k := by linarith
  have hH : N/2 ≤ N-2*k+s := by linarith
  have hMle : N-k ≤ N := by linarith
  have hhalf : 1/2 ≤ N*(N-2*k+s)/(N-k)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hM)).mpr
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hH),
      mul_nonneg hk (show 0 ≤ 2*N-k by linarith)]
  have hNs : N*s ≤ 3*k^2 := by
    have h := (le_div_iff₀ hN).mp hs3
    nlinarith
  have hdiff : |N*(N-2*k+s)-(N-k)^2| ≤ 2*k^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hN.le hs0, sq_nonneg k]
  have hr : |N*(N-2*k+s)/(N-k)^2-1| ≤ 2*k^2/(N-k)^2 := by
    rw [show N*(N-2*k+s)/(N-k)^2-1 =
      (N*(N-2*k+s)-(N-k)^2)/(N-k)^2 by field_simp,
      abs_div, abs_of_pos (sq_pos_of_pos hM)]
    exact div_le_div_of_nonneg_right hdiff (sq_nonneg _)
  calc
    _ = (N-k) * |Real.log (N*(N-2*k+s)/(N-k)^2)| := by rw [abs_mul, abs_of_pos hM]
    _ ≤ (N-k) * (2*(2*k^2/(N-k)^2)) :=
      mul_le_mul_of_nonneg_left ((abs_log_le_twice_sub_one _ hhalf).trans
        (mul_le_mul_of_nonneg_left hr (by norm_num))) hM.le
    _ = 4*k^2/(N-k) := by field_simp; ring
    _ ≤ 8*k^2/N := by
      apply (div_le_div_iff₀ hM hN).mpr
      nlinarith [mul_nonneg (sq_nonneg k) (show 0 ≤ N-2*k by linarith)]

theorem dense_factorial_deletion_log (n k : ℕ) (hn : 0 < n) (hk : 2*k ≤ n) :
    |Real.log ((n:ℝ)^k * ((n-k).factorial:ℝ)/(n.factorial:ℝ))| ≤ 2*(k:ℝ)^2/n := by
  have hp : (0:ℝ) < (n:ℝ)^k * ((n-k).factorial:ℝ)/(n.factorial:ℝ) := by positivity
  rw [abs_of_nonneg (Real.log_nonneg (factorial_deletion_ratio_one_le n k (by omega)))]
  exact (Real.log_le_iff_le_exp hp).mpr (factorial_deletion_ratio_le_exp n k hn hk)

theorem DenseStochastic.minor_mass_log {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n))
    (hk : (U.card:ℝ) ≤ (n:ℝ)/16) :
    |(Fintype.card (Uᶜ : Finset (Fin n)):ℝ) *
      Real.log ((n:ℝ)*matrixEntryMass (densePrincipalMinor D U) /
        (Fintype.card (Uᶜ : Finset (Fin n)):ℝ)^2)| ≤ 8*(U.card:ℝ)^2/n := by
  have hM : (Fintype.card (Uᶜ : Finset (Fin n)):ℝ) = (n:ℝ)-U.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (show U.card ≤ n by simpa using U.card_le_univ)]
  rw [hM,hD.deleted_mass U]
  exact dense_minor_mass_log_scalar n U.card (denseRemovedMass D U)
    (by exact_mod_cast hn) (Nat.cast_nonneg _) hk (hD.removed_mass_bounds U).1
    (hD.removed_mass_bounds U).2.2

end TournamentHamiltonian
