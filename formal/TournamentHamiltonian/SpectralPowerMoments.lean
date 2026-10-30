module

public import TournamentHamiltonian.MatrixPowerDefs
public import TournamentHamiltonian.SkewSpectrum
public import TournamentHamiltonian.ComplexSpectralFrobenius

/-!
# All positive paired spectral moments and actual real matrix powers

Multiplicity is preserved by the existing Multiset frequency decomposition.
The positivity of the exponent is essential when removing zero frequencies.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open Matrix
open scoped Matrix

theorem complexFrobeniusSq_unitary_conjugation {n : ℕ}
    (U : unitary (Matrix (Fin n) (Fin n) ℂ)) (M : Matrix (Fin n) (Fin n) ℂ) :
    complexFrobeniusSq (Unitary.conjStarAlgAut ℂ _ U M) = complexFrobeniusSq M := by
  rw [complexFrobeniusSq_eq_trace_gram, complexFrobeniusSq_eq_trace_gram]
  change ((Unitary.conjStarAlgAut ℂ _ U M) *
    star (Unitary.conjStarAlgAut ℂ _ U M)).trace.re = (M * star M).trace.re
  rw [← map_star, ← map_mul, portedSkewSpectrum_trace_unitary_conjugation]

theorem complexFrobeniusSq_of_real_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    complexFrobeniusSq (Complex.ofRealHom.mapMatrix A) = matrixFrobSq A := by
  change (∑ i, ∑ j, ‖(A i j : ℂ)‖ ^ 2) = ∑ i, ∑ j, A i j ^ 2
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem imaginary_frequency_power_norm_sq (x : ℝ) (p : ℕ) :
    ‖(-Complex.I * (x : ℂ)) ^ p‖ ^ 2 = x ^ (2 * p) := by
  calc
    _ = (|x| ^ p) ^ 2 := by simp [norm_pow, norm_mul]
    _ = (|x| ^ 2) ^ p := by rw [← pow_mul, Nat.mul_comm p 2, pow_mul]
    _ = (x ^ 2) ^ p := by rw [sq_abs]
    _ = _ := (pow_mul x 2 p).symm

/-- Complete, Fin-indexed frequency power sum, including every multiplicity. -/
theorem skewFrequency_even_pow_sum_eq_frob {n : ℕ} (T : Tournament n) (p : ℕ) :
    (∑ i, skewFrequency T i ^ (2 * p)) = matrixFrobSq ((signMatrix T) ^ p) := by
  let U := (skewHermitian_isHermitian T).eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => -Complex.I * (skewFrequency T i : ℂ))
  have hdiag : complexSignMatrix T = Unitary.conjStarAlgAut ℂ _ U D :=
    complexSignMatrix_unitary_diagonalization T
  have hmap : Complex.ofRealHom.mapMatrix ((signMatrix T) ^ p) =
      (complexSignMatrix T) ^ p := by
    rw [map_pow]
    rfl
  symm
  calc
    _ = complexFrobeniusSq ((complexSignMatrix T) ^ p) := by
      rw [← hmap, complexFrobeniusSq_of_real_matrix]
    _ = complexFrobeniusSq (D ^ p) := by
      rw [hdiag, ← map_pow, complexFrobeniusSq_unitary_conjugation]
    _ = _ := by
      simp only [D, Matrix.diagonal_pow, Pi.pow_apply, Matrix.diagonal_apply,
        complexFrobeniusSq, apply_ite, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      simp [imaginary_frequency_power_norm_sq]
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul, Nat.mul_comm p 2, pow_mul, sq_abs, ← pow_mul]

theorem positiveSkewFrequencies_even_pow_sum {n : ℕ} (T : Tournament n)
    (p : ℕ) (hp : 0 < p) :
    (∑ i, skewFrequency T i ^ (2 * p)) =
      2 * ((positiveSkewFrequencies T).map (fun x => x ^ (2 * p))).sum := by
  classical
  let M := Finset.univ.val.map (skewFrequency T)
  have hz : ((M.filter (fun x => x = 0)).map (fun x => x ^ (2 * p))).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    simp only [Multiset.mem_filter] at hx
    simp [hx.2, show 2 * p ≠ 0 by omega]
  have hneg : (((positiveSkewFrequencies T).map (fun x => -x)).map
      (fun x => x ^ (2 * p))).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ (2 * p))).sum := by
    simp only [Multiset.map_map, Function.comp_def, pow_mul, neg_sq]
  have hsum : (M.map (fun x => x ^ (2 * p))).sum =
      ∑ i, skewFrequency T i ^ (2 * p) := by
    simp only [M, Multiset.map_map, Function.comp_def, Finset.sum_map_val]
  have h := skewFrequency_multiset_decomposition T
  change M = _ at h
  rw [h, Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add, hneg, hz] at hsum
  linarith

/-- Exact normalization of the positive-frequency List, before pairing. -/
theorem pairedMasses_pow_sum_eq_positive {n : ℕ} (T : Tournament n) (p : ℕ) :
    ((pairedMasses T).map (fun x => x ^ p)).sum =
      ((positiveSkewFrequencies T).map (fun x => x ^ (2 * p))).sum / (n : ℝ) ^ (2 * p) := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe]
  simp only [pairedMasses, Multiset.coe_toList,
    Multiset.map_map, Function.comp_def]
  have hterm : ∀ x : ℝ, (x ^ 2 / (n : ℝ) ^ 2) ^ p =
      x ^ (2 * p) / (n : ℝ) ^ (2 * p) := by
    intro x
    rw [div_pow, ← pow_mul, ← pow_mul]
  simp_rw [hterm]
  induction positiveSkewFrequencies T using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp [ih, add_div]

/-- The all-positive-power identity with the genuine real sign-matrix power.
Both the factor 2 and the denominator exponent 2p are retained explicitly. -/
theorem pairedMasses_pow_sum_eq_frob {n : ℕ} (T : Tournament n)
    (_hn : 0 < n) (p : ℕ) (hp : 0 < p) :
    ((pairedMasses T).map (fun x => x ^ p)).sum =
      matrixFrobSq ((signMatrix T) ^ p) / (2 * (n : ℝ) ^ (2 * p)) := by
  have hpair := positiveSkewFrequencies_even_pow_sum T p hp
  rw [skewFrequency_even_pow_sum_eq_frob] at hpair
  rw [pairedMasses_pow_sum_eq_positive, hpair]
  ring

theorem spectral_involutive_conjugation_pow {n : ℕ}
    (D A : Matrix (Fin n) (Fin n) ℝ) (hD : D * D = 1) (p : ℕ) :
    (D * A * D) ^ p = D * (A ^ p) * D := by
  induction p with
  | zero => simpa using hD.symm
  | succ p ih =>
    rw [pow_succ, ih]
    calc
      _ = D * (A ^ p) * (D * D) * A * D := by noncomm_ring
      _ = D * (A ^ (p + 1)) * D := by rw [hD, Matrix.mul_one, pow_succ]; noncomm_ring

/-- Signed diagonal switching preserves every Frobenius power mass, not only
the determinant ratio.  The alternating comparison in the current endpoint
therefore has the same complete moment table as the transitive tournament. -/
theorem matrixFrobSq_alternating_pow (n p : ℕ) :
    matrixFrobSq ((signMatrix (alternatingTournament n)) ^ p) =
      matrixFrobSq ((signMatrix (transitiveTournament n)) ^ p) := by
  rw [signMatrix_alternatingTournament, signMatrix_transitiveTournament,
    alternatingSkew_signed_conjugation,
    spectral_involutive_conjugation_pow _ _ (alternatingDiagonal_mul_self n)]
  unfold matrixFrobSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [alternatingDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_pow, alternatingSign_sq, one_mul, mul_one]

theorem pairedMasses_alternating_transitive_pow_sum (n : ℕ) (hn : 0 < n)
    (p : ℕ) (hp : 0 < p) :
    ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum =
      ((pairedMasses (transitiveTournament n)).map (fun x => x ^ p)).sum := by
  rw [pairedMasses_pow_sum_eq_frob _ hn p hp, pairedMasses_pow_sum_eq_frob _ hn p hp,
    matrixFrobSq_alternating_pow]

end TournamentHamiltonian
