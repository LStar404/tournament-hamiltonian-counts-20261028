module

public import Tournament.HessianCoordinateBridge
public import Tournament.HessianCoordinates
public import Tournament.HessianLogNormalization
public import Tournament.ScalarTwoJet
public import Tournament.OriginalCoordinates

/-!
# The actual Wormald angle Hessian for a regular tournament

The angle function in this file is the logarithm of the explicit branch of the
original determinant `det(I-(A+I/2)diag(y))`, evaluated at `y_j=(2/d)exp(iθ_j)`.
The eliminated last input coordinate is held at `2/d`. The Hessian is defined by
actual iterated real Fréchet derivatives of this complex-valued function; it is
not defined as the proposed matrix, and no real-part projection is taken.
-/

@[expose] public section

open Filter Matrix
open scoped Topology Matrix

namespace Tournament.HessianMain

set_option backward.isDefEq.respectTransparency false

open HessianCoordinates HessianCoordinateBridge

/-- The original angle function in the manuscript, with exactly `n` real inputs. -/
noncomputable def originalAngle {n : ℕ} (T : TournamentPaths.Tournament (Fin (n + 1)))
    (θ : Fin n → ℝ) : ℂ :=
  Complex.log (HessianBranch.branch (OriginalCoordinates.originalMatrix T) (Fin.last n)
    (HessianBranch.expCoordinates (OriginalCoordinates.coordinateScale (ι := Fin (n + 1)))
      (Complex.I • realIncludeFirst n θ)))

/-- The actual Hessian entries, with both differentiations over the real angle
variables and with the full complex value retained. -/
noncomputable def angleHessian {n : ℕ} (T : TournamentPaths.Tournament (Fin (n + 1))) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k => fderiv ℝ (fderiv ℝ (originalAngle T)) 0 (Pi.single j 1) (Pi.single k 1)

/-- The normalized analytic angle calculation for any real skew matrix with
zero row sums. Its proof uses the actual resolvent derivatives and actual
local determinant branch, with no postulated two-jet or branch nondegeneracy. -/
theorem normalized_angle_second {n : ℕ}
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hskew : Cᵀ = -C) (hrow : C *ᵥ (fun _ => 1) = 0)
    (a : ℂ) (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (fun θ => a +
      HessianBranch.logBranch (RankOneEquation.P0 (Fintype.card (Fin (n + 1))) +
        C.map Complex.ofReal) (Fin.last n) 1 (Complex.I • realIncludeFirst n θ))) 0 v w =
      matrixBilinear ((HessianAlgebra.resolvent C).map Complex.ofReal)
        (compressedDirection n v) (compressedDirection n w) := by
  let Cc := C.map Complex.ofReal
  let d : ℂ := Fintype.card (Fin (n + 1))
  let N := RankOneEquation.P0 d + Cc
  let g := HessianBranch.logBranch N (Fin.last n) 1
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcRow : Cc *ᵥ (fun _ => 1) = 0 :=
    ScalarTwoJet.complexification_mulVec_one_zero C hrow
  have hcCol : (fun _ => 1) ᵥ* Cc = 0 :=
    ScalarTwoJet.complexification_one_vecMul_zero C hskew hrow
  have hu : IsUnit (1 - Cc) := RankOneEquation.one_sub_complex_skew_isUnit C hskew
  have hdet : IsUnit (1 - Cc).det := hu.map Matrix.detMonoidHom
  have hφ : AnalyticAt ℂ (RankOneEquation.phi d Cc) 0 :=
    ScalarTwoJet.analyticAt_phi d Cc 0 (by simpa [ResolventDerivatives.pencil] using hu)
  have hg : AnalyticAt ℂ g 0 :=
    RankOneEquation.analyticAt_logBranch Cc (Fin.last n) hcRow hcCol hdet
  have hg0 : g 0 = 0 := HessianBranch.logBranch_zero N (Fin.last n) one_ne_zero
    (RankOneEquation.K₁_one_ne_zero Cc (Fin.last n) hcRow hcCol hdet)
    (RankOneEquation.K_one_eq_zero Cc hcRow hdet)
  have hz : (fun t => RankOneEquation.phi d Cc
      (clear (Fin.last n) t + insert (Fin.last n) (g t))) =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)]
        fun _ => 0 := by
    simpa only [clear_add_insert, d, g, N, Filter.EventuallyEq] using
      RankOneEquation.logBranch_local_phi_zero Cc (Fin.last n) hcRow hcCol hdet
  have hf : ∀ z, fderiv ℂ (RankOneEquation.phi d Cc) 0 z = -mass z / d := by
    intro z
    simpa only [mass_apply] using ScalarTwoJet.fderiv_phi_zero_real_skew d C z hskew hrow
  have hs : ∀ z t, fderiv ℂ (fderiv ℂ (RankOneEquation.phi d Cc)) 0 z t =
      -matrixBilinear ((HessianAlgebra.resolvent C).map Complex.ofReal) z t / d := by
    intro z t
    simpa only [matrixBilinear_apply] using
      ScalarTwoJet.iterated_fderiv_phi_zero_real_skew d C z t hskew hrow
  have h := real_angle_coordinate_hessian
    (clear (Fin.last n)) (insert (Fin.last n)) mass
    (matrixBilinear ((HessianAlgebra.resolvent C).map Complex.ofReal)) hd
    (mass_insert (Fin.last n)) hφ hg hg0 hz hf hs (realIncludeFirst n) a v w
  exact h

/-- The actual normalized determinant branch is analytic and passes through one,
with both facts derived solely from regularity of the Boolean tournament. -/
theorem regular_normalized_branch_data {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n + 1))) (hT : TournamentPaths.IsRegular T) :
    AnalyticAt ℂ (HessianBranch.branch (OriginalCoordinates.normalizedMatrix T)
      (Fin.last n)) (fun _ => 1) ∧
    HessianBranch.branch (OriginalCoordinates.normalizedMatrix T)
      (Fin.last n) (fun _ => 1) = 1 := by
  let C := TournamentPaths.normalizedSign T
  have hskew := TournamentPaths.normalizedSign_skew T
  have hr := TournamentPaths.regular_normalizedSign_mulVec_one T hT
  have hcRow := ScalarTwoJet.complexification_mulVec_one_zero C hr
  have hcCol := ScalarTwoJet.complexification_one_vecMul_zero C hskew hr
  have hu := RankOneEquation.one_sub_complex_skew_isUnit C hskew
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hn := RankOneEquation.K₁_one_ne_zero (C.map Complex.ofReal) (Fin.last n)
    hcRow hcCol hdet
  have hz := RankOneEquation.K_one_eq_zero (C.map Complex.ofReal) hcRow hdet
  constructor
  · exact HessianBranch.analyticAt_branch _ _ _ hn
  · exact HessianBranch.branch_at_base _ _ _ hn hz

/-- Equality with the original angle function is an actual neighborhood equality
of logarithms. Positive real scaling fixes the branch; no equality merely modulo
`2πi`, or merely after exponentiation, is used. -/
theorem originalAngle_eventually_eq {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n + 1))) (hT : TournamentPaths.IsRegular T) :
    originalAngle T =ᶠ[𝓝 (0 : Fin n → ℝ)] fun θ =>
      Complex.log (OriginalCoordinates.coordinateScale (ι := Fin (n + 1))) +
      HessianBranch.logBranch (OriginalCoordinates.normalizedMatrix T) (Fin.last n) 1
        (Complex.I • realIncludeFirst n θ) := by
  obtain ⟨hb, hb0⟩ := regular_normalized_branch_data T hT
  let N := OriginalCoordinates.normalizedMatrix T
  let H : (Fin n → ℝ) → ℂ := fun θ => HessianBranch.branch N (Fin.last n)
    (HessianBranch.expCoordinates 1 (Complex.I • realIncludeFirst n θ))
  have hrot : ContinuousAt (fun θ : Fin n → ℝ => Complex.I • realIncludeFirst n θ) 0 :=
    ((realIncludeFirst n).continuous.const_smul Complex.I).continuousAt
  have hexp : ContinuousAt (fun θ : Fin n → ℝ =>
      HessianBranch.expCoordinates 1 (Complex.I • realIncludeFirst n θ)) 0 := by
    have he : ContinuousAt (HessianBranch.expCoordinates (1 : ℂ))
        (Complex.I • realIncludeFirst n (0 : Fin n → ℝ)) := by
      simpa using (HessianBranch.analyticAt_expCoordinates (n := Fin (n + 1)) 1 0).continuousAt
    exact ContinuousAt.comp (f := fun θ : Fin n → ℝ => Complex.I • realIncludeFirst n θ)
      (x := 0) he hrot
  have hc : ContinuousAt H 0 := by
    have hb' : ContinuousAt (HessianBranch.branch N (Fin.last n))
        (HessianBranch.expCoordinates 1 (Complex.I • realIncludeFirst n (0 : Fin n → ℝ))) := by
      simpa [N] using hb.continuousAt
    exact ContinuousAt.comp (f := fun θ : Fin n → ℝ =>
      HessianBranch.expCoordinates 1 (Complex.I • realIncludeFirst n θ)) (x := 0) hb' hexp
  have hH0 : H 0 = 1 := by simpa [H, N] using hb0
  filter_upwards [hc.eventually_ne (show H 0 ≠ 0 by rw [hH0]; exact one_ne_zero)] with θ hθ
  unfold originalAngle
  rw [OriginalCoordinates.original_branch_expCoordinates]
  have hlog := Complex.log_ofReal_mul
    (OriginalCoordinates.realCoordinateScale_pos (ι := Fin (n + 1))) hθ
  rw [OriginalCoordinates.realCoordinateScale_cast,
    Complex.ofReal_log (OriginalCoordinates.realCoordinateScale_pos (ι := Fin (n + 1))).le,
    OriginalCoordinates.realCoordinateScale_cast] at hlog
  simpa only [H, N, HessianBranch.logBranch, div_one] using hlog

/-- The original complex-valued angle's real second derivative is the asserted
real matrix form, complexified entrywise. -/
theorem original_angle_second {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n + 1))) (hT : TournamentPaths.IsRegular T)
    (v w : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (originalAngle T)) 0 v w =
      matrixBilinear ((HessianAlgebra.resolvent (TournamentPaths.normalizedSign T)).map
        Complex.ofReal) (compressedDirection n v) (compressedDirection n w) := by
  rw [(originalAngle_eventually_eq T hT).fderiv.fderiv_eq]
  exact normalized_angle_second (TournamentPaths.normalizedSign T)
    (TournamentPaths.normalizedSign_skew T)
    (TournamentPaths.regular_normalizedSign_mulVec_one T hT)
    (Complex.log (OriginalCoordinates.coordinateScale (ι := Fin (n + 1)))) v w

/-- The manuscript's Hessian identity for an actual regular Boolean tournament.
All derivative, local-branch, inverse, and coefficient-nonvanishing facts have
been proved; regularity is the sole extra hypothesis beyond the tournament type.
The equality retains the actual complex derivative values and proves them real. -/
theorem angleHessian_eq_compressedResolvent {n : ℕ}
    (T : TournamentPaths.Tournament (Fin (n + 1))) (hT : TournamentPaths.IsRegular T) :
    angleHessian T = (HessianAlgebra.compressedResolvent n
      (TournamentPaths.normalizedSign T)).map Complex.ofReal := by
  ext j k
  change fderiv ℝ (fderiv ℝ (originalAngle T)) 0 (Pi.single j 1) (Pi.single k 1) = _
  rw [original_angle_second T hT, compressed_matrixBilinear_entry]
  rfl

end Tournament.HessianMain
