module

public import Tournament.SharpAsymptoticComponents
public import TournamentHamiltonian.TransitiveCotSpectrum

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- The cotangent cap for the real Euclidean operator norm of an actual graph. -/
theorem signMatrix_real_opNorm_le_cot {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖signMatrix T‖ ≤ Real.cot (Real.pi / (2 * n)) := by
  have hmap : Complex.ofRealHom.mapMatrix (signMatrix T) = complexSignMatrix T := rfl
  exact ((real_matrix_opNorm_le_complexification (signMatrix T)).trans_eq
    (congrArg norm hmap)).trans (signMatrix_complex_opNorm_le_cot T hn)

end TournamentHamiltonian

namespace TournamentPaths

/-- The manuscript's real sign matrix satisfies the full cotangent cap. -/
theorem signMatrix_opNorm_le_cot {n : ℕ} (T : Tournament (Fin n)) (hn : 0 < n) :
    ‖signMatrix T‖ ≤ Real.cot (Real.pi / (2 * n)) := by
  simpa only [signMatrix_toLegacy] using
    TournamentHamiltonian.signMatrix_real_opNorm_le_cot (toLegacy T) hn

theorem signMatrix_opNorm_lt_two_mul_div_pi {n : ℕ} (T : Tournament (Fin n))
    (hn : 0 < n) : ‖signMatrix T‖ < 2 * n / Real.pi :=
  (signMatrix_opNorm_le_cot T hn).trans_lt
    (TournamentHamiltonian.transitive_cot_lt_two_mul_div_pi n hn)

/-- This is the older packing constant C_*, not a renamed sharp constant L. -/
theorem pathSpectralRatio_le_upperConstant {n : ℕ} (T : Tournament (Fin n))
    (hn : 0 < n) : pathSpectralRatio T ≤ TournamentHamiltonian.upperConstant :=
  TournamentHamiltonian.spectralRatio_le_upperConstant (toLegacy T) hn

end TournamentPaths
