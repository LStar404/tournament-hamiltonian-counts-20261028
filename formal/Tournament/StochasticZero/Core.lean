module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators Matrix

@[expose] public section

namespace StochasticZero

variable {ι : Type*} [Fintype ι]

/-- A convex combination of points in the closed complex unit disk can equal `1`
only when every point of positive weight equals `1`. -/
theorem disk_barycenter_rigid (p : ι → ℝ) (z : ι → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hz : ∀ j, ‖z j‖ ≤ 1) (havg : ∑ j, (p j : ℂ) * z j = 1) :
    ∀ j, 0 < p j → z j = 1 := by
  classical
  have hre : ∑ j, p j * (z j).re = 1 := by
    simpa using congrArg Complex.re havg
  have hnonneg : ∀ j, 0 ≤ p j * (1 - (z j).re) := by
    intro j
    exact mul_nonneg (hp j) (sub_nonneg.mpr ((Complex.re_le_norm (z j)).trans (hz j)))
  have hzero : ∑ j, p j * (1 - (z j).re) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hsum, hre, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hzero
  intro j hj
  have hrej : (z j).re = 1 := by
    have := (mul_eq_zero.mp (hterm j (Finset.mem_univ j))).resolve_left (ne_of_gt hj)
    linarith
  have himj : (z j).im = 0 := by
    have hnorm := Complex.sq_norm_sub_sq_re (z j)
    have hn0 := norm_nonneg (z j)
    have hn1 := hz j
    nlinarith [sq_nonneg ((z j).im)]
  exact Complex.ext (by simpa using hrej) (by simpa using himj)

/-- Positive entries of a row-stochastic matrix give directed edges. -/
def PositiveReachable (P : Matrix ι ι ℝ) (i j : ι) : Prop :=
  Relation.ReflTransGen (fun i j => 0 < P i j) i j

/-- Equality at a maximum-modulus row forces all supported summands to equal that row. -/
theorem maximal_row_rigid (P : Matrix ι ι ℝ) (u v : ι → ℂ)
    (hp : ∀ i j, 0 ≤ P i j) (hsum : ∀ i, ∑ j, P i j = 1)
    (hu : ∀ j, ‖u j‖ ≤ 1)
    (hv : ∀ i, v i = ∑ j, (P i j : ℂ) * u j * v j)
    (i : ι) (hi0 : v i ≠ 0) (hmax : ∀ j, ‖v j‖ ≤ ‖v i‖) :
    ∀ j, 0 < P i j → u j * v j = v i := by
  classical
  have hi_norm : 0 < ‖v i‖ := norm_pos_iff.mpr hi0
  have hbound : ∀ j, ‖u j * v j / v i‖ ≤ 1 := by
    intro j
    rw [norm_div, norm_mul, div_le_one hi_norm]
    exact (mul_le_mul_of_nonneg_right (hu j) (norm_nonneg (v j))).trans
      (by simpa using hmax j)
  have havg : ∑ j, (P i j : ℂ) * (u j * v j / v i) = 1 := by
    calc
      _ = (∑ j, (P i j : ℂ) * u j * v j) / v i := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = v i / v i := by rw [← hv i]
      _ = 1 := div_self hi0
  have hrigid := disk_barycenter_rigid (P i) (fun j => u j * v j / v i)
    (hp i) (hsum i) hbound havg
  intro j hj
  exact (div_eq_one_iff_eq hi0).mp (hrigid j hj)

/-- Finite stochastic maximum principle with positive diagonal and strongly
connected support. There are no assumed spectral or uniqueness claims. -/
theorem fixed_vector_rigidity [Nonempty ι]
    (P : Matrix ι ι ℝ) (u v : ι → ℂ)
    (hp : ∀ i j, 0 ≤ P i j) (hsum : ∀ i, ∑ j, P i j = 1)
    (hdiag : ∀ i, 0 < P i i)
    (hconn : ∀ i j, PositiveReachable P i j)
    (hu : ∀ j, ‖u j‖ ≤ 1) (hv0 : v ≠ 0)
    (hv : ∀ i, v i = ∑ j, (P i j : ℂ) * u j * v j) :
    (∀ j, u j = 1) ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ j, v j = c := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
    Finset.univ_nonempty
  have hmax : ∀ j, ‖v j‖ ≤ ‖v k‖ := fun j => hk j (Finset.mem_univ j)
  have hk0 : v k ≠ 0 := by
    intro hkz
    apply hv0
    funext j
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [hkz] using hmax j) (norm_nonneg _)
  have hkpos : 0 < ‖v k‖ := norm_pos_iff.mpr hk0
  have hstep : ∀ i j, ‖v i‖ = ‖v k‖ → 0 < P i j → ‖v j‖ = ‖v k‖ := by
    intro i j hi hij
    have hi0 : v i ≠ 0 := norm_pos_iff.mp (by rw [hi]; exact hkpos)
    have hrow := maximal_row_rigid P u v hp hsum hu hv i hi0
      (fun l => by rw [hi]; exact hmax l) j hij
    have hle : ‖v k‖ ≤ ‖v j‖ := by
      calc
        ‖v k‖ = ‖u j * v j‖ := by rw [hrow, hi]
        _ = ‖u j‖ * ‖v j‖ := norm_mul _ _
        _ ≤ 1 * ‖v j‖ := mul_le_mul_of_nonneg_right (hu j) (norm_nonneg _)
        _ = ‖v j‖ := one_mul _
    exact le_antisymm (hmax j) hle
  have hmod : ∀ j, ‖v j‖ = ‖v k‖ := by
    intro j
    have hpath := hconn k j
    induction hpath with
    | refl => rfl
    | @tail a b hpath hab ih => exact hstep a b ih hab
  have hnz : ∀ j, v j ≠ 0 := by
    intro j
    apply norm_pos_iff.mp
    rw [hmod j]
    exact hkpos
  have hrow : ∀ i j, 0 < P i j → u j * v j = v i := by
    intro i
    exact maximal_row_rigid P u v hp hsum hu hv i (hnz i)
      (fun j => by rw [hmod j, hmod i])
  have hone : ∀ j, u j = 1 := by
    intro j
    apply mul_right_cancel₀ (hnz j)
    simpa using hrow j j (hdiag j)
  refine ⟨hone, v k, hk0, ?_⟩
  intro j
  have hpath := hconn k j
  induction hpath with
  | refl => rfl
  | @tail a b hpath hab ih =>
      have hedge : v b = v a := by simpa [hone b] using hrow a b hab
      exact hedge.trans ih

/-- The genuine complex matrix whose determinant controls the finite zero set. -/
def twistedMatrix [DecidableEq ι] (P : Matrix ι ι ℝ) (u : ι → ℂ) : Matrix ι ι ℂ :=
  1 - Matrix.of (fun i j => (P i j : ℂ)) * Matrix.diagonal u

/-- Kernel equation of the genuine twisted matrix, in row-sum form. -/
theorem twistedMatrix_mulVec_eq_zero_iff [DecidableEq ι]
    (P : Matrix ι ι ℝ) (u v : ι → ℂ) :
    twistedMatrix P u *ᵥ v = 0 ↔
      ∀ i, v i = ∑ j, (P i j : ℂ) * u j * v j := by
  rw [twistedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_diagonal] using congrFun h i
  · intro h
    funext i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_diagonal] using h i

/-- Exact closed-polydisk zero locus. Nonzero kernels are obtained from the
actual determinant, not supplied as an extra uniqueness premise. -/
theorem det_twistedMatrix_eq_zero_iff [Nonempty ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (u : ι → ℂ)
    (hp : ∀ i j, 0 ≤ P i j) (hsum : ∀ i, ∑ j, P i j = 1)
    (hdiag : ∀ i, 0 < P i i)
    (hconn : ∀ i j, PositiveReachable P i j)
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    (twistedMatrix P u).det = 0 ↔ ∀ j, u j = 1 := by
  constructor
  · intro hdet
    obtain ⟨v, hv0, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact (fixed_vector_rigidity P u v hp hsum hdiag hconn hu hv0
      ((twistedMatrix_mulVec_eq_zero_iff P u v).mp hker)).1
  · intro hone
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro hzero
      have := congrFun hzero (Classical.arbitrary ι)
      simp at this
    · apply (twistedMatrix_mulVec_eq_zero_iff P u (fun _ => 1)).mpr
      intro i
      simp only [hone, mul_one]
      exact_mod_cast (hsum i).symm

omit [Fintype ι] in
/-- Converting genuine paths in the positive-entry quiver to explicit
reflexive/transitive positive-edge reachability. -/
theorem positiveReachable_of_quiver_path (P : Matrix ι ι ℝ) (i j : ι)
    (p : @Quiver.Path ι (Matrix.toQuiver P) i j) : PositiveReachable P i j := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons p e ih => exact ih.tail e.down

omit [Fintype ι] in
/-- The graph-language interface required by the stochastic zero theorem. -/
theorem positiveReachable_of_stronglyConnected (P : Matrix ι ι ℝ)
    (hconn : @Quiver.IsStronglyConnected ι (Matrix.toQuiver P)) :
    ∀ i j, PositiveReachable P i j := by
  intro i j
  obtain ⟨p⟩ := hconn i j
  exact positiveReachable_of_quiver_path P i j p

/-- A convenient matrix-irreducibility version of the exact zero-locus result. -/
theorem det_twistedMatrix_eq_zero_iff_of_irreducible [Nonempty ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (u : ι → ℂ)
    (hP : P.IsIrreducible) (hsum : ∀ i, ∑ j, P i j = 1)
    (hdiag : ∀ i, 0 < P i i) (hu : ∀ j, ‖u j‖ ≤ 1) :
    (twistedMatrix P u).det = 0 ↔ ∀ j, u j = 1 := by
  exact det_twistedMatrix_eq_zero_iff P u hP.nonneg hsum hdiag
    (positiveReachable_of_stronglyConnected P
      (@Quiver.IsSStronglyConnected.isStronglyConnected ι (Matrix.toQuiver P) hP.connected)) hu

/-- The hypothesis stated directly in the standard positive-entry quiver API. -/
theorem fixed_vector_rigidity_of_stronglyConnected [Nonempty ι]
    (P : Matrix ι ι ℝ) (u v : ι → ℂ)
    (hp : ∀ i j, 0 ≤ P i j) (hsum : ∀ i, ∑ j, P i j = 1)
    (hdiag : ∀ i, 0 < P i i)
    (hconn : @Quiver.IsStronglyConnected ι (Matrix.toQuiver P))
    (hu : ∀ j, ‖u j‖ ≤ 1) (hv0 : v ≠ 0)
    (hv : ∀ i, v i = ∑ j, (P i j : ℂ) * u j * v j) :
    (∀ j, u j = 1) ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ j, v j = c := by
  exact fixed_vector_rigidity P u v hp hsum hdiag
    (positiveReachable_of_stronglyConnected P hconn) hu hv0 hv

/-- Standard-quiver version of the exact zero-locus equivalence. -/
theorem det_twistedMatrix_eq_zero_iff_of_stronglyConnected [Nonempty ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (u : ι → ℂ)
    (hp : ∀ i j, 0 ≤ P i j) (hsum : ∀ i, ∑ j, P i j = 1)
    (hdiag : ∀ i, 0 < P i i)
    (hconn : @Quiver.IsStronglyConnected ι (Matrix.toQuiver P))
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    (twistedMatrix P u).det = 0 ↔ ∀ j, u j = 1 := by
  exact det_twistedMatrix_eq_zero_iff P u hp hsum hdiag
    (positiveReachable_of_stronglyConnected P hconn) hu

end StochasticZero
