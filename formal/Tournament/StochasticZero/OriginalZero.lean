module

public import Tournament.StochasticZero.TournamentBridge
public import Tournament.OriginalCoordinates

set_option autoImplicit false
open scoped BigOperators Matrix

@[expose] public section

namespace StochasticZero

/-- Identity-preserving conversion between the two existing tournament structures. -/
def toHamiltonian {n : ℕ} (T : TournamentPaths.Tournament (Fin n)) :
    TournamentHamiltonian.Tournament n :=
  ⟨T.edge, T.loopless, T.oriented⟩

theorem toHamiltonian_adjacency {n : ℕ} (T : TournamentPaths.Tournament (Fin n)) :
    TournamentHamiltonian.adjacency (toHamiltonian T) = TournamentPaths.adjacency T := rfl

theorem toHamiltonian_regular_rows {n : ℕ} (T : TournamentPaths.Tournament (Fin n))
    (hT : TournamentPaths.IsRegular T) :
    ∀ i, ∑ j, TournamentHamiltonian.adjacency (toHamiltonian T) i j = ((n : ℝ) - 1) / 2 := by
  intro i
  rw [toHamiltonian_adjacency, TournamentPaths.adjacency_row_sum]
  have h : 2 * (TournamentPaths.outDegree T i : ℝ) + 1 = n := by
    have h := hT i
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  linarith

open Tournament.OriginalCoordinates Tournament.HessianBranch

/-- The normalized complex matrix is exactly the complexification of the
lazy real matrix; there is no change of zero-locus object. -/
theorem lazyTournament_complex_original {n : ℕ}
    (T : TournamentPaths.Tournament (Fin n)) :
    Matrix.of (fun i j => (lazyTournament (toHamiltonian T) i j : ℂ)) =
      coordinateScale (ι := Fin n) • originalMatrix T := by
  ext i j
  simp only [Matrix.of_apply, lazyTournament, toHamiltonian_adjacency,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_add, originalMatrix, coordinateScale,
    Fintype.card_fin, Matrix.smul_apply, Matrix.add_apply,
    Tournament.HessianAlgebra.complexOfReal, RingHom.mapMatrix_apply, Matrix.map_apply,
    Complex.ofRealHom_eq_coe, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- The original manuscript determinant at scaled coordinates is the same
actual determinant used by the stochastic rigidity theorem. -/
theorem original_K_eq_twisted {n : ℕ} (T : TournamentPaths.Tournament (Fin n))
    (u : Fin n → ℂ) :
    K (originalMatrix T) (coordinateScale (ι := Fin n) • u) =
      (twistedMatrix (lazyTournament (toHamiltonian T)) u).det := by
  rw [K_scale, ← lazyTournament_complex_original]
  rfl

/-- Global unique zero in the whole closed polydisk in original coordinates.
This includes its torus boundary; it does not assert any coefficient asymptotics. -/
theorem original_K_zero_iff {n : ℕ} (T : TournamentPaths.Tournament (Fin n))
    (hn : 0 < n) (hT : TournamentPaths.IsRegular T)
    (y : Fin n → ℂ)
    (hy : ∀ j, ‖y j‖ ≤ realCoordinateScale (ι := Fin n)) :
    K (originalMatrix T) y = 0 ↔
      ∀ j, y j = coordinateScale (ι := Fin n) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hzpos : 0 < realCoordinateScale (ι := Fin n) := realCoordinateScale_pos
  have hz0 : coordinateScale (ι := Fin n) ≠ 0 := coordinateScale_ne_zero
  have hznorm : ‖coordinateScale (ι := Fin n)‖ = realCoordinateScale (ι := Fin n) := by
    rw [← realCoordinateScale_cast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
  let u : Fin n → ℂ := fun j => y j / coordinateScale (ι := Fin n)
  have hu : ∀ j, ‖u j‖ ≤ 1 := by
    intro j
    dsimp [u]
    rw [norm_div, hznorm, div_le_one hzpos]
    exact hy j
  have hyu : y = coordinateScale (ι := Fin n) • u := by
    funext j
    dsimp [u]
    field_simp
  have hzero := regular_tournament_zero_locus (toHamiltonian T) hn
    (toHamiltonian_regular_rows T hT) u hu
  rw [hyu, original_K_eq_twisted, hzero]
  constructor
  · intro hone j
    simp [hone j]
  · intro hone j
    have h := hone j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ hz0 (by simpa using h)

end StochasticZero
