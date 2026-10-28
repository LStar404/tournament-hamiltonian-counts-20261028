module

public import Tournament.HessianMain
public import Tournament.SignMatrix

/-!
# The Wormald angle Hessian theorem, with its complete source object

The left side below is the second real derivative of the original complex-valued
angle function. The real matrix is supplied as a witness only after its equality
with that derivative has been proved. Positive definiteness, the exact determinant,
and the positive rational square-root conclusion are then bundled together.

No counting asymptotic theorem or unproved Hessian identity is a hypothesis.
-/

public section

open Matrix
open scoped Matrix

namespace Tournament

/-- Full Hessian result corresponding to manuscript Theorems 1.2 / 9.2.
The manuscript uses odd `d ≥ 3`; this theorem is valid for every existing regular
tournament on `n+1` vertices (and therefore in particular in that range).
`normalizedSign T` is the actual sign matrix divided by the vertex count.
-/
theorem wormald_original_angle_hessian {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n + 1))) (hT : TournamentPaths.IsRegular T) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ,
      HessianMain.angleHessian T = H.map Complex.ofReal ∧
      H = HessianAlgebra.compressedResolvent n (TournamentPaths.normalizedSign T) ∧
      H.PosDef ∧
      0 < H.det ∧
      H.det = ((n + 1 : ℕ) : ℝ) *
        (1 + TournamentPaths.normalizedSign T * TournamentPaths.normalizedSign T).det /
        (1 - TournamentPaths.normalizedSign T * TournamentPaths.normalizedSign T).det ∧
      ∃ q : ℚ, 0 < q ∧
        Real.sqrt (((n + 1 : ℕ) : ℝ) / H.det) = (q : ℝ) ∧
        (q : ℂ) =
          (1 + HessianAlgebra.complexOfReal (TournamentPaths.normalizedSign T)).det /
          (1 + Complex.I •
            HessianAlgebra.complexOfReal (TournamentPaths.normalizedSign T)).det := by
  refine ⟨HessianAlgebra.compressedResolvent n (TournamentPaths.normalizedSign T),
    HessianMain.angleHessian_eq_compressedResolvent T hT, rfl, ?_, ?_, ?_, ?_⟩
  · exact TournamentPaths.tournament_algebraicHessian_posDef T
  · exact (TournamentPaths.tournament_algebraicHessian_posDef T).det_pos
  · exact TournamentPaths.regular_tournament_algebraicHessian_det T hT
  · exact TournamentPaths.regular_tournament_positive_rational_sqrt T hT

end Tournament
