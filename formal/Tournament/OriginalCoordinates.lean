module

public import Tournament.SignMatrix
public import Tournament.RankOneEquation
public import Tournament.ScalarTwoJet

/-!
# Exact scaling from the manuscript's original determinant coordinates

The manuscript uses `M = A + I/2` and the basepoint `z = 2/d`.
The normalized resolvent calculation uses `P₀ + C`, with `C = S/d`.
This file proves the exact matrix, determinant, and explicit-branch scaling
identities connecting those two constructions for actual tournaments.
-/

@[expose] public section

open Matrix
open scoped Matrix Topology
open Filter

namespace Tournament.OriginalCoordinates

open HessianBranch

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Move a uniform scalar from the determinant coordinates to its fixed matrix. -/
theorem K_scale (M : Matrix ι ι ℂ) (z : ℂ) (y : ι → ℂ) :
    K M (z • y) = K (z • M) y := by
  unfold K
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
lemma update_scale (z : ℂ) (y : ι → ℂ) (j : ι) (w : ℂ) :
    Function.update (z • y) j (z * w) = z • Function.update y j w := by
  ext i
  by_cases hi : i = j <;> simp [hi, Function.update_of_ne, Pi.smul_apply, smul_eq_mul]

theorem K₀_scale (M : Matrix ι ι ℂ) (z : ℂ) (j : ι) (y : ι → ℂ) :
    K₀ M j (z • y) = K₀ (z • M) j y := by
  unfold K₀
  have hu := update_scale z y j 0
  simp only [mul_zero] at hu
  rw [hu, K_scale]

theorem K₁_scale (M : Matrix ι ι ℂ) (z : ℂ) (j : ι) (y : ι → ℂ) :
    z * K₁ M j (z • y) = K₁ (z • M) j y := by
  have h : K M (Function.update (z • y) j z) =
      K (z • M) (Function.update y j 1) := by
    have hu := update_scale z y j 1
    simp only [mul_one] at hu
    rw [hu, K_scale]
  rw [K_update_affine, K_update_affine, K₀_scale, one_mul] at h
  exact add_left_cancel h

/-- The explicit quotient branch scales exactly; no local approximation is used. -/
theorem branch_scale (M : Matrix ι ι ℂ) (z : ℂ) (hz : z ≠ 0)
    (j : ι) (y : ι → ℂ) :
    branch M j (z • y) = z * branch (z • M) j y := by
  unfold branch
  rw [← K₀_scale M z j y, ← K₁_scale M z j y]
  by_cases hc : K₁ M j (z • y) = 0
  · simp [hc]
  · field_simp

/-- Original fixed matrix `A + I/2`, with adjacency taken from the actual graph. -/
noncomputable def originalMatrix (T : TournamentPaths.Tournament ι) : Matrix ι ι ℂ :=
  HessianAlgebra.complexOfReal (TournamentPaths.adjacency T) + (2 : ℂ)⁻¹ • 1

/-- Original basepoint `z = 2/d`. -/
noncomputable def coordinateScale : ℂ := (2 : ℂ) / Fintype.card ι

/-- The same basepoint as a real number, for the original angle function. -/
noncomputable def realCoordinateScale : ℝ := (2 : ℝ) / Fintype.card ι

omit [DecidableEq ι] in
theorem realCoordinateScale_cast :
    (realCoordinateScale (ι := ι) : ℂ) = coordinateScale (ι := ι) := by
  simp [realCoordinateScale, coordinateScale]

omit [DecidableEq ι] in
theorem realCoordinateScale_pos [Nonempty ι] : 0 < realCoordinateScale (ι := ι) := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

/-- The normalized matrix used by the rank-one resolvent reduction. -/
noncomputable def normalizedMatrix (T : TournamentPaths.Tournament ι) : Matrix ι ι ℂ :=
  RankOneEquation.P0 (Fintype.card ι) +
    HessianAlgebra.complexOfReal (TournamentPaths.normalizedSign T)

/-- Exact graph-derived identity `(2/d)(A+I/2) = P₀ + S/d`. -/
theorem normalized_originalMatrix (T : TournamentPaths.Tournament ι) :
    coordinateScale (ι := ι) • originalMatrix T = normalizedMatrix T := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [coordinateScale, originalMatrix, normalizedMatrix, RankOneEquation.P0,
      HessianAlgebra.complexOfReal, TournamentPaths.normalizedSign,
      TournamentPaths.signMatrix_diag, Matrix.smul_apply, div_eq_mul_inv]
    ring
  · have hp : ((TournamentPaths.adjacency T i j : ℝ) : ℂ) +
        ((TournamentPaths.adjacency T j i : ℝ) : ℂ) = 1 := by
      exact_mod_cast TournamentPaths.adjacency_pair T i j hij
    simp only [coordinateScale, originalMatrix, normalizedMatrix, RankOneEquation.P0,
      HessianAlgebra.complexOfReal, RingHom.mapMatrix_apply, Matrix.map_apply,
      Complex.ofRealHom_eq_coe,
      Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply, hij, ↓reduceIte,
      mul_zero, add_zero, TournamentPaths.normalizedSign, TournamentPaths.signMatrix,
      Matrix.sub_apply, Matrix.transpose_apply, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_sub, div_eq_mul_inv]
    linear_combination (Fintype.card ι : ℂ)⁻¹ * hp

/-- Original determinant in uniformly scaled coordinates equals the normalized one. -/
theorem original_K_scaled (T : TournamentPaths.Tournament ι) (y : ι → ℂ) :
    K (originalMatrix T) (coordinateScale (ι := ι) • y) = K (normalizedMatrix T) y := by
  rw [K_scale, normalized_originalMatrix]

/-- The manuscript's exponential coordinates feed the same normalized determinant. -/
theorem original_K_expCoordinates (T : TournamentPaths.Tournament ι) (t : ι → ℂ) :
    K (originalMatrix T) (expCoordinates (coordinateScale (ι := ι)) t) =
      K (normalizedMatrix T) (fun i => Complex.exp (t i)) := by
  exact original_K_scaled T (fun i => Complex.exp (t i))

omit [DecidableEq ι] in
theorem coordinateScale_ne_zero [Nonempty ι] : coordinateScale (ι := ι) ≠ 0 := by
  exact div_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Original and normalized last-coordinate branches differ by exactly `z=2/d`. -/
theorem original_branch_scaled [Nonempty ι] (T : TournamentPaths.Tournament ι)
    (j : ι) (y : ι → ℂ) :
    branch (originalMatrix T) j (coordinateScale (ι := ι) • y) =
      coordinateScale (ι := ι) * branch (normalizedMatrix T) j y := by
  rw [branch_scale _ _ coordinateScale_ne_zero, normalized_originalMatrix]

/-- Branch scaling in precisely the manuscript's exponential coordinates. -/
theorem original_branch_expCoordinates [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (j : ι) (t : ι → ℂ) :
    branch (originalMatrix T) j (expCoordinates (coordinateScale (ι := ι)) t) =
      coordinateScale (ι := ι) * branch (normalizedMatrix T) j (expCoordinates 1 t) := by
  have h0 : expCoordinates (coordinateScale (ι := ι)) t =
      coordinateScale (ι := ι) • (fun i => Complex.exp (t i)) := by
    funext i
    rfl
  have h1 : expCoordinates (1 : ℂ) t = (fun i => Complex.exp (t i)) := by
    funext i
    change (1 : ℂ) * Complex.exp (t i) = Complex.exp (t i)
    rw [one_mul]
  rw [h0, h1]
  exact original_branch_scaled T j (fun i => Complex.exp (t i))

private theorem regular_normalized_base_nondegenerate [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    K₁ (normalizedMatrix T) j (fun _ => 1) ≠ 0 ∧
      K (normalizedMatrix T) (fun _ => 1) = 0 := by
  let C := TournamentPaths.normalizedSign T
  have hs := TournamentPaths.normalizedSign_skew T
  have hr := TournamentPaths.regular_normalizedSign_mulVec_one T hT
  have hrow := ScalarTwoJet.complexification_mulVec_one_zero C hr
  have hcol := ScalarTwoJet.complexification_one_vecMul_zero C hs hr
  have hu := RankOneEquation.one_sub_complex_skew_isUnit C hs
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  exact ⟨RankOneEquation.K₁_one_ne_zero (C.map Complex.ofReal) j hrow hcol hd,
    RankOneEquation.K_one_eq_zero (C.map Complex.ofReal) hrow hd⟩

/-- The actual original-coordinate coefficient is nonzero at `y=z·1`.
This is derived from the regular tournament, not assumed as an implicit-function hypothesis. -/
theorem regular_original_K₁_ne_zero [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    K₁ (originalMatrix T) j (fun _ => coordinateScale (ι := ι)) ≠ 0 := by
  have hn := (regular_normalized_base_nondegenerate T hT j).1
  have hs := K₁_scale (originalMatrix T) (coordinateScale (ι := ι)) j (fun _ => 1)
  rw [normalized_originalMatrix] at hs
  have he : coordinateScale (ι := ι) • (fun _ : ι => (1 : ℂ)) =
      (fun _ => coordinateScale (ι := ι)) := by
    funext i
    simp
  rw [he] at hs
  intro hz
  rw [hz, mul_zero] at hs
  exact hn hs.symm

/-- The original determinant vanishes at the genuine basepoint `z=2/d`. -/
theorem regular_original_K_base_zero [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) :
    K (originalMatrix T) (fun _ => coordinateScale (ι := ι)) = 0 := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  have hz := (regular_normalized_base_nondegenerate T hT j).2
  have hs := original_K_scaled T (fun _ => 1)
  have he : coordinateScale (ι := ι) • (fun _ : ι => (1 : ℂ)) =
      (fun _ => coordinateScale (ι := ι)) := by
    funext i
    simp
  rw [he, hz] at hs
  exact hs

/-- The original branch `h(y')` is genuinely analytic near `z·1` for each
regular tournament. The selected input coordinate is ignored by the branch. -/
theorem regular_original_branch_analytic [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    AnalyticAt ℂ (branch (originalMatrix T) j) (fun _ => coordinateScale (ι := ι)) :=
  HessianBranch.analyticAt_branch _ _ _ (regular_original_K₁_ne_zero T hT j)

/-- The original analytic branch passes through its stated basepoint. -/
theorem regular_original_branch_base [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    branch (originalMatrix T) j (fun _ => coordinateScale (ι := ι)) =
      coordinateScale (ι := ι) :=
  HessianBranch.branch_at_base _ _ _ (regular_original_K₁_ne_zero T hT j)
    (regular_original_K_base_zero T hT)

/-- The original determinant zero set is locally exactly the graph of `h`. -/
theorem regular_original_branch_local_unique [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    ∀ᶠ y in 𝓝 (fun _ : ι => coordinateScale (ι := ι)), ∀ w : ℂ,
      K (originalMatrix T) (Function.update y j w) = 0 ↔
        w = branch (originalMatrix T) j y :=
  HessianBranch.branch_local_unique _ _ _ (regular_original_K₁_ne_zero T hT j)

/-- The unnormalized principal logarithm of the actual original branch is
analytic: its base value is positive real, hence away from the logarithm cut. -/
theorem regular_original_rawLog_analytic [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    AnalyticAt ℂ (fun y => Complex.log (branch (originalMatrix T) j y))
      (fun _ => coordinateScale (ι := ι)) := by
  apply (regular_original_branch_analytic T hT j).clog
  rw [regular_original_branch_base T hT j, ← realCoordinateScale_cast]
  exact Complex.ofReal_mem_slitPlane.mpr realCoordinateScale_pos

/-- The original logarithm remains analytic in the manuscript's exponential
coordinates, before restriction to the real angle variables. -/
theorem regular_original_rawLog_exp_analytic [Nonempty ι]
    (T : TournamentPaths.Tournament ι) (hT : TournamentPaths.IsRegular T) (j : ι) :
    AnalyticAt ℂ (fun t => Complex.log (branch (originalMatrix T) j
      (expCoordinates (coordinateScale (ι := ι)) t))) 0 := by
  have ha := regular_original_rawLog_analytic T hT j
  have hc := HessianBranch.analyticAt_expCoordinates (n := ι)
    (coordinateScale (ι := ι)) 0
  have ha' : AnalyticAt ℂ (fun y => Complex.log (branch (originalMatrix T) j y))
      (expCoordinates (coordinateScale (ι := ι)) (0 : ι → ℂ)) := by
    simpa using ha
  exact ha'.comp hc

end Tournament.OriginalCoordinates
