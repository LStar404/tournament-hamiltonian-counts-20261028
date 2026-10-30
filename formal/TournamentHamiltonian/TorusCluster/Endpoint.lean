module

public import TournamentHamiltonian.TorusCluster.Product

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

/-- End-to-end finite cluster theorem. Its only inputs are the real angle
configuration, actual simple graph, m≥64, and the actual degree bound.
No cross-edge or core cardinal lower bound is supplied as a hypothesis. -/
theorem finite_cluster_bounds (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ m) (x : Fin m → ℝ) :
    ∃ j : Fin 16, (m:ℝ)/16 ≤ (core x (center j)).card ∧
      (((m:ℝ)/4 ≤ (far x (center j)).card ∧
        (m:ℝ)^2/128 ≤ (crossEdges H (far x (center j)) (core x (center j))).card ∧
        kernel H x ≤ Real.exp (-kappa0*(m:ℝ)^2/128)) ∨
       (3*(m:ℝ)/4 < (inner x (center j)).card ∧
        ((outliers x (center j)).card : ℝ) < (m:ℝ)/4 ∧
        (m:ℝ)*(outliers x (center j)).card/2 ≤
          (crossEdges H (outliers x (center j)) (inner x (center j))).card ∧
        kernel H x ≤ Real.exp (-kappa1*(m:ℝ)*(outliers x (center j)).card/2) *
          insideProduct H x (outer x (center j)))) := by
  obtain ⟨j,hj⟩ := exists_large_core x
  refine ⟨j,hj,?_⟩
  by_cases hf : (m:ℝ)/4 ≤ (far x (center j)).card
  · exact Or.inl ⟨hf,
      far_cross_count H hdegree hm _ _ (far_core_disjoint x _) hf hj,
      far_kernel_bound H hdegree hm x _ hj hf⟩
  · have hf' := lt_of_not_ge hf
    have hI := inner_large_of_not_far x (center j) hf'
    exact Or.inr ⟨hI, outliers_lt_quarter_of_not_far x _ hf',
      outlier_cross_count H hdegree hm _ _ (outliers_inner_disjoint x _) hI,
      outlier_kernel_bound H hdegree hm x _ hf'⟩

lemma edgeFactor_repr (x : Fin m → ℝ) (c : ℝ) (e : Sym2 (Fin m)) :
    edgeFactor (fun i => repr (x i) c) e = edgeFactor x e := by
  induction e using Sym2.ind with
  | _ i j => exact repr_sub_cos (x i) (x j) c

lemma insideProduct_repr (H : SimpleGraph (Fin m)) (x : Fin m → ℝ)
    (c : ℝ) (A : Finset (Fin m)) :
    insideProduct H (fun i => repr (x i) c) A = insideProduct H x A := by
  unfold insideProduct
  apply Finset.prod_congr rfl
  intro e _
  exact edgeFactor_repr x c e

/-- The consistent representatives really are in a short real interval; their
differences, unlike arbitrary original representatives, equal circle distances. -/
theorem outer_short_arc (x : Fin m → ℝ) (c : ℝ) {i j : Fin m}
    (hi : i ∈ outer x c) (hj : j ∈ outer x c) :
    |repr (x i) c - repr (x j) c| ≤ 3*Real.pi/8 ∧
    circleDist (x i) (x j) = |repr (x i) c - repr (x j) c| := by
  have hi' : circleDist (x i) c ≤ 3*Real.pi/16 := (mem_arc _ _ _ _).mp hi
  have hj' : circleDist (x j) c ≤ 3*Real.pi/16 := (mem_arc _ _ _ _).mp hj
  have hb := short_arc_real_difference hi' hj'
  have hb' : |repr (x i) c-repr (x j) c| ≤ 3*Real.pi/8 := by linarith
  refine ⟨hb', ?_⟩
  rw [← circleDist_repr (x i) (x j) c]
  apply circleDist_eq_abs
  linarith [Real.pi_pos]

/-- All-local case, including the distinguished root whenever it is one of the
vertices: no vertex can disappear from the short-arc certificate. -/
theorem local_short_arc (x : Fin m → ℝ) (c : ℝ)
    (hr : (outliers x c).card = 0) :
    (∀ i, |repr (x i) c| ≤ 3*Real.pi/16) ∧
    (∀ i j, |repr (x i) c-repr (x j) c| ≤ 3*Real.pi/8 ∧
      circleDist (x i) (x j) = |repr (x i) c-repr (x j) c|) := by
  have hall (i : Fin m) : i ∈ outer x c := by
    have he : outliers x c = ∅ := Finset.card_eq_zero.mp hr
    by_contra hi
    have hb : i ∈ outliers x c := Finset.mem_compl.mpr hi
    rw [he] at hb
    exact Finset.notMem_empty _ hb
  constructor
  · intro i
    rw [abs_repr]
    exact (mem_arc _ _ _ _).mp (hall i)
  · intro i j
    exact outer_short_arc x c (hall i) (hall j)

end
end TorusCluster
