module

public import TournamentHamiltonian.DenseGramScaling
public import TournamentHamiltonian.RectangularPermanentUnconditional

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def denseFullPermanentConstant : ℝ := uniformPermanentActivityConstant 4 (4/5)
noncomputable def denseScaledPermanentConstant : ℝ := uniformPermanentActivityConstant 13 (19/20)

theorem densePermanentConstants_nonneg :
    0 ≤ denseFullPermanentConstant ∧ 0 ≤ denseScaledPermanentConstant :=
  ⟨uniformPermanentActivityConstant_nonneg _ _ (by norm_num) (by norm_num),
    uniformPermanentActivityConstant_nonneg _ _ (by norm_num) (by norm_num)⟩

theorem dense_rectangularPermanent_refl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι ℝ) : @rectangularPermanent ι ι _ (Classical.decEq ι) Y (Equiv.refl ι) = Y.permanent := by
  unfold rectangularPermanent
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
  exact congrArg (fun d : DecidableEq ι => @Matrix.permanent ι d _ ℝ _ Y)
    (Subsingleton.elim _ _)

theorem dense_gramGaussian_decEq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ ℝ) : @gramGaussian ι κ _ _ (Classical.decEq κ) Z = gramGaussian Z :=
  congrArg (fun d : DecidableEq κ => @gramGaussian ι κ _ _ d Z) (Subsingleton.elim _ _)

theorem dense_gramGaussian_one_le_of_gap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ ℝ) (hgap : ‖Z‖ < 1) : 1 ≤ gramGaussian Z := by
  have h := gramGaussian_one_le_of_gap Z hgap
  rw [dense_gramGaussian_decEq] at h
  exact h

theorem dense_gramGaussian_pos_of_gap {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (Z : Matrix ι κ ℝ) (hgap : ‖Z‖ < 1) : 0 < gramGaussian Z :=
  lt_of_lt_of_le (by norm_num) (dense_gramGaussian_one_le_of_gap Z hgap)

/-- Actual full permanent approximation; no error or activity predicate is assumed. -/
theorem DenseStochastic.permanent_relative {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) :
    |(((n : ℝ)^n / (n.factorial : ℝ)) * D.permanent) /
      gramGaussian (denseBaseKernel D) - 1| ≤ denseFullPermanentConstant / n := by
  have ha : rectangularAverageMatrix (Fin n) (Fin n) = averagingMatrix (Fin n) := by
    ext i j; simp [rectangularAverageMatrix, averagingMatrix]
  have hgap : ‖D-rectangularAverageMatrix (Fin n) (Fin n)‖ ≤ (4/5:ℝ) := by
    rw [ha]; exact hD.gap
  have hd : ∀ i j, |D i j| ≤ 3 / Fintype.card (Fin n) := by
    intro i j
    simpa only [abs_of_nonneg (hD.nonnegative i j), Fintype.card_fin] using hD.density i j
  have h := rectangularPermanent_relative_from_matrix_bounds D (Equiv.refl _)
    (by simpa using hn) 3 (4/5) (by norm_num) (by norm_num) (by norm_num)
    hD.row_sum hD.column_sum hd hgap
  rw [ha] at h
  rw [dense_rectangularPermanent_refl, dense_gramGaussian_decEq] at h
  norm_num only at h
  simpa only [Fintype.card_fin, denseBaseKernel, denseFullPermanentConstant] using h

/-- Independent lower bound for the actual full permanent; no cycle/path input. -/
theorem DenseStochastic.permanent_lower {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n)
    (hlarge : 2*denseFullPermanentConstant ≤ (n:ℝ)) :
    (n.factorial:ℝ)/(2*(n:ℝ)^n) ≤ D.permanent := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have ha : 0 < (n:ℝ)^n/(n.factorial:ℝ) := by positivity
  have hG := dense_gramGaussian_one_le_of_gap (denseBaseKernel D)
    (hD.gap.trans_lt (by norm_num))
  have hGp : 0 < gramGaussian (denseBaseKernel D) := by linarith
  have he : denseFullPermanentConstant/n ≤ (1/2:ℝ) :=
    (div_le_iff₀ hnR).mpr (by linarith)
  have hr : (1/2:ℝ) ≤ ((n:ℝ)^n/(n.factorial:ℝ))*D.permanent/gramGaussian (denseBaseKernel D) := by
    have h := (abs_le.mp (hD.permanent_relative hn)).1
    linarith
  have hm : (1/2:ℝ) ≤ ((n:ℝ)^n/(n.factorial:ℝ))*D.permanent := by
    calc
      _ ≤ (((n:ℝ)^n/(n.factorial:ℝ))*D.permanent/gramGaussian (denseBaseKernel D))*
          gramGaussian (denseBaseKernel D) :=
        hr.trans (le_mul_of_one_le_right (by linarith) hG)
      _ = _ := div_mul_cancel₀ _ hGp.ne'
  have h := (div_le_iff₀ ha).mpr (show (1/2:ℝ) ≤ D.permanent*((n:ℝ)^n/(n.factorial:ℝ)) by nlinarith)
  convert h using 1 <;> field_simp <;> ring

/-- Actual permanent approximation for the same balanced matrix in the Gram chain. -/
theorem DenseStochastic.scaled_permanent_relative {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16)
    (z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ)
    (hz : LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
      6 9 (9 / 10) (8 * (U.card : ℝ) / n) z) :
    |(((Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) ^ Fintype.card (Uᶜ : Finset (Fin n)) /
        ((Fintype.card (Uᶜ : Finset (Fin n))).factorial : ℝ)) *
          (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z).permanent) /
      gramGaussian (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
        averagingMatrix (Uᶜ : Finset (Fin n))) - 1| ≤
          denseScaledPermanentConstant / Fintype.card (Uᶜ : Finset (Fin n)) := by
  let Y := localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z
  have hp := (hD.minor_basic hn U hk).1
  have ha : rectangularAverageMatrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) =
      averagingMatrix (Uᶜ : Finset (Fin n)) := by
    ext i j; simp [rectangularAverageMatrix, averagingMatrix]
  have hgap : ‖Y-rectangularAverageMatrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n))‖ ≤ (19/20:ℝ) := by
    rw [ha]; exact hz.gap.trans (by norm_num)
  have hd : ∀ i j, |Y i j| ≤ 12 / Fintype.card (Uᶜ : Finset (Fin n)) := by
    intro i j
    convert hz.density i j using 1; ring
  have h := rectangularPermanent_relative_from_matrix_bounds Y (Equiv.refl _)
    hp 12 (19/20) (by norm_num) (by norm_num) (by norm_num)
    hz.row_sum hz.column_sum hd hgap
  rw [ha] at h
  rw [dense_rectangularPermanent_refl, dense_gramGaussian_decEq] at h
  norm_num only at h
  simpa only [denseScaledPermanentConstant] using h

/-- Elementary positivity extraction from a genuine relative approximation. -/
theorem positive_of_actual_relative_error (p a G e : ℝ) (ha : 0 < a) (hG : 0 < G)
    (he : e < 1) (h : |a*p/G-1| ≤ e) : 0 < p := by
  have hr : 0 < a*p/G := by have hh := (abs_le.mp h).1; linarith
  have hprod := mul_pos hr hG
  rw [div_mul_cancel₀ _ hG.ne'] at hprod
  by_contra hp
  have hnon := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hp)
  linarith


end TournamentHamiltonian
