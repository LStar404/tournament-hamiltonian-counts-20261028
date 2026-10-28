module

public import Tournament.HessianRationality
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Positive determinant quotient and selection of the positive square root

This closes the sign issue left by the squared determinant identities. Positivity
is proved by a nonvanishing continuous homotopy, not inferred from equal squares.
The result concerns the algebraic Hessian candidate, before its analytic bridge.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace Tournament.HessianAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def complexOfReal (C : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  Complex.ofRealHom.mapMatrix C

lemma complexOfReal_skew (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (complexOfReal C)ᵀ = -complexOfReal C := by
  ext i j
  have h := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [complexOfReal, h]

lemma real_imaginary_perturbation_hermitian (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (1 + Complex.I • complexOfReal C).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [complexOfReal, Matrix.one_apply, h, eq_comm]

noncomputable def imaginaryDet (C : Matrix ι ι ℝ) : ℝ :=
  (1 + Complex.I • complexOfReal C).det.re

lemma imaginaryDet_cast (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (imaginaryDet C : ℂ) = (1 + Complex.I • complexOfReal C).det := by
  apply Complex.conj_eq_iff_re.mp
  change star (1 + Complex.I • complexOfReal C).det = _
  rw [← Matrix.det_conjTranspose]
  exact congrArg Matrix.det (real_imaginary_perturbation_hermitian C hC).eq

lemma complexOfReal_det (M : Matrix ι ι ℝ) :
    ((M.det : ℝ) : ℂ) = (complexOfReal M).det := by
  exact Complex.ofRealHom.map_det M

lemma imaginaryDet_sq (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    imaginaryDet C ^ 2 = (1 + C * C).det := by
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_pow, imaginaryDet_cast C hC, complexOfReal_det,
    ← det_one_add_square_complex _ (complexOfReal_skew C hC)]
  congr 1
  simp [complexOfReal, map_add, map_mul]

omit [DecidableEq ι] in
lemma frobeniusSq_nonneg (C : Matrix ι ι ℝ) : 0 ≤ frobeniusSq C := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
lemma frobeniusSq_smul (C : Matrix ι ι ℝ) (t : ℝ) :
    frobeniusSq (t • C) = t ^ 2 * frobeniusSq C := by
  simp [frobeniusSq, mul_pow, Finset.mul_sum]

omit [DecidableEq ι] in
lemma frobeniusSq_smul_lt_one (C : Matrix ι ι ℝ) (hF : frobeniusSq C < 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : frobeniusSq (t • C) < 1 := by
  rw [frobeniusSq_smul]
  have hsq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  calc
    t ^ 2 * frobeniusSq C ≤ 1 * frobeniusSq C :=
      mul_le_mul_of_nonneg_right hsq (frobeniusSq_nonneg C)
    _ < 1 := by simpa using hF

lemma imaginaryDet_ne_zero (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : imaginaryDet C ≠ 0 := by
  have hpos := (one_add_square_posDef C hC hF).det_pos
  rw [← imaginaryDet_sq C hC] at hpos
  exact fun h => by simp [h] at hpos

lemma imaginaryDet_homotopy_continuous (C : Matrix ι ι ℝ) :
    Continuous (fun t : ℝ => imaginaryDet (t • C)) := by
  unfold imaginaryDet
  apply Complex.continuous_re.comp
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => (if i = j then (1 : ℂ) else 0) +
    Complex.I * (((t * C i j : ℝ) : ℂ)))
  fun_prop

lemma positive_at_one_of_nonvanishing (f : ℝ → ℝ)
    (hc : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (h0 : 0 < f 0)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) : 0 < f 1 := by
  by_contra h
  have hf1 : f 1 ≤ 0 := le_of_not_gt h
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
    (show (0 : ℝ) ∈ Set.Icc (f 1) (f 0) from ⟨hf1, h0.le⟩)
  exact hne t ht hft

/-- The complex determinant in the denominator is strictly positive and real. -/
theorem imaginaryDet_pos (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : 0 < imaginaryDet C := by
  have h := positive_at_one_of_nonvanishing (fun t => imaginaryDet (t • C))
    (imaginaryDet_homotopy_continuous C).continuousOn ?_ ?_
  · simpa using h
  · simp [imaginaryDet, complexOfReal]
  · intro t ht
    apply imaginaryDet_ne_zero
    · simp [Matrix.transpose_smul, hC]
    · exact frobeniusSq_smul_lt_one C hF t ht

/-- Positivity of the real numerator requires skewness but no small-norm bound. -/
theorem real_perturbation_det_pos (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    0 < (1 + C).det := by
  have hc : Continuous (fun t : ℝ => (1 + t • C).det) := by fun_prop
  have h := positive_at_one_of_nonvanishing (fun t => (1 + t • C).det)
    hc.continuousOn (by simp) ?_
  · simpa using h
  · intro t _
    have hsk : (-t • C)ᵀ = -(-t • C) := by simp [Matrix.transpose_smul, hC]
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp (one_sub_skew_isUnit (-t • C) hsk)
    have hne := hu.ne_zero
    simpa using hne

noncomputable def realDeterminantRatio (C : Matrix ι ι ℝ) : ℝ :=
  (1 + C).det / imaginaryDet C

theorem realDeterminantRatio_pos (C : Matrix ι ι ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) : 0 < realDeterminantRatio C :=
  div_pos (real_perturbation_det_pos C hC) (imaginaryDet_pos C hC hF)

lemma realDeterminantRatio_cast (C : Matrix ι ι ℝ) (hC : Cᵀ = -C) :
    (realDeterminantRatio C : ℂ) =
      (1 + complexOfReal C).det / (1 + Complex.I • complexOfReal C).det := by
  rw [realDeterminantRatio, Complex.ofReal_div, imaginaryDet_cast C hC, complexOfReal_det]
  congr 2
  change Complex.ofRealHom.mapMatrix (1 + C) = 1 + Complex.ofRealHom.mapMatrix C
  rw [map_add, map_one]

/-- The positive-square-root identity, with the sign proved rather than assumed. -/
theorem sqrt_compressedResolvent_det (n : ℕ)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hC : Cᵀ = -C)
    (hF : frobeniusSq C < 1) (hzero : C *ᵥ (fun _ => 1) = 0) :
    Real.sqrt (((n + 1 : ℕ) : ℝ) / (compressedResolvent n C).det) =
      realDeterminantRatio C := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hnum : (1 + C).det ≠ 0 := (real_perturbation_det_pos C hC).ne'
  have hden : imaginaryDet C ≠ 0 := (imaginaryDet_pos C hC hF).ne'
  have hquot : (((n + 1 : ℕ) : ℝ)) / (compressedResolvent n C).det =
      realDeterminantRatio C ^ 2 := by
    rw [compressedResolvent_det n C hC hzero, det_one_sub_square C hC,
      ← imaginaryDet_sq C hC]
    unfold realDeterminantRatio
    field_simp
  rw [hquot, Real.sqrt_sq (realDeterminantRatio_pos C hC hF).le]

/-- The rational matrix viewed over the real field. -/
noncomputable def realOfRat (C : Matrix ι ι ℚ) : Matrix ι ι ℝ :=
  (Rat.castHom ℝ).mapMatrix C

lemma realOfRat_skew (C : Matrix ι ι ℚ) (hC : Cᵀ = -C) :
    (realOfRat C)ᵀ = -realOfRat C := by
  ext i j
  have h := congrFun (congrFun hC i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp [realOfRat, h]

lemma complexOfReal_realOfRat (C : Matrix ι ι ℚ) :
    complexOfReal (realOfRat C) = complexOfRat C := by
  ext i j
  simp [complexOfReal, realOfRat, complexOfRat]

/-- Exact positive rational witness for the square root in the paper's algebraic
Hessian formula.  All contraction and zero-row-sum assumptions are explicit;
the actual tournament bridge derives them from its graph definition. -/
theorem positive_rational_sqrt_compressed (n : ℕ)
    (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hC : Cᵀ = -C)
    (hF : frobeniusSq (realOfRat C) < 1)
    (hzero : realOfRat C *ᵥ (fun _ => 1) = 0) :
    ∃ q : ℚ, 0 < q ∧
      Real.sqrt (((n + 1 : ℕ) : ℝ) / (compressedResolvent n (realOfRat C)).det) = (q : ℝ) ∧
      (q : ℂ) = (1 + complexOfRat C).det / (1 + Complex.I • complexOfRat C).det := by
  obtain ⟨q, hq⟩ := determinant_ratio_rational C hC
  have hCr := realOfRat_skew C hC
  have hcast : (realDeterminantRatio (realOfRat C) : ℂ) = (q : ℂ) := by
    rw [realDeterminantRatio_cast _ hCr, complexOfReal_realOfRat]
    exact hq.symm
  have hqR : realDeterminantRatio (realOfRat C) = (q : ℝ) := by
    simpa using congrArg Complex.re hcast
  have hposR : (0 : ℝ) < q := by
    rw [← hqR]
    exact realDeterminantRatio_pos _ hCr hF
  have hpos : (0 : ℚ) < q := by exact_mod_cast hposR
  refine ⟨q, hpos, ?_, hq⟩
  rw [sqrt_compressedResolvent_det n _ hCr hF hzero, hqR]

end Tournament.HessianAlgebra
