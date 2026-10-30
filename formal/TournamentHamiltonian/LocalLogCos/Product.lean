module

public import TournamentHamiltonian.LocalLogCos.Scalar
public import TournamentHamiltonian.RootGaussianTail.Coordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic RootObservable PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def retainedEnergy (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j), (rootLift x i-rootLift x j)^2

def remainderSum (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j), remainder (rootLift x i-rootLift x j)

def cosProduct (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j), Real.cos (rootLift x i-rootLift x j)

def rootBox (r : ℝ) (x : Fin n → ℝ) : Prop := ∀ i, |x i| ≤ r

theorem laplacian_unordered_energy {m : ℕ} (F : EdgeSet m) (y : Fin m → ℝ) :
    y ⬝ᵥ laplacian F *ᵥ y =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), if (graph F).Adj i j then (y i-y j)^2 else 0 := by
  have h := (graph F).lapMatrix_toLinearMap₂' ℝ y
  simp only [Matrix.toLinearMap₂'_apply'] at h
  have ho := ordered_eq_twice_upper (fun i j => if (graph F).Adj i j then (y i-y j)^2 else 0)
    (fun i j => by
      have he : (y i-y j)^2 = (y j-y i)^2 := by ring
      simp only [(graph F).adj_comm i j, he]) (fun i => by simp)
  rw [ho] at h
  change y ⬝ᵥ laplacian F *ᵥ y = _ at h
  linarith

theorem retainedEnergy_eq_root_quadratic (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    retainedEnergy F x = x ⬝ᵥ rootMatrix F *ᵥ x := by
  have hsplit : retainedEnergy F x + rootLift x ⬝ᵥ laplacian F *ᵥ rootLift x =
      RootGaussianTail.pairEnergy (n+1) (rootLift x) := by
    rw [laplacian_unordered_energy]
    simp only [retainedEnergy, RootGaussianTail.pairEnergy, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i<j <;> by_cases ha : (graph F).Adj i j <;> simp [h,ha]
  rw [root_quadratic_identity, gaugeMatrix, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_sub,
    dotProduct_smul, ones_mulVec, dotProduct_smul, dot_one]
  rw [RootGaussianTail.pairEnergy_moments] at hsplit
  have hsq : rootLift x ⬝ᵥ rootLift x = ∑ i, (rootLift x i)^2 := by simp [dotProduct, pow_two]
  rw [hsq]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one] at hsplit ⊢
  linarith

theorem rootLift_abs_le {r : ℝ} (hr : 0 ≤ r) {x : Fin n → ℝ} (hx : rootBox r x)
    (i : Fin (n+1)) : |rootLift x i| ≤ r := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hr
  · exact hx j

theorem root_difference_le {r : ℝ} (hr : 0 ≤ r) {x : Fin n → ℝ} (hx : rootBox r x)
    (i j : Fin (n+1)) : |rootLift x i-rootLift x j| ≤ 2*r := by
  exact (abs_sub _ _).trans (by linarith [rootLift_abs_le hr hx i, rootLift_abs_le hr hx j])

theorem root_difference_quarter {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) (i j : Fin (n+1)) :
    |rootLift x i-rootLift x j| ≤ Real.pi/4 := by
  have h := root_difference_le hr hx i j
  linarith

theorem log_sum_identity (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j), logCos (rootLift x i-rootLift x j)) =
      -retainedEnergy F x/2-rootQuartic F x+remainderSum F x := by
  simp only [remainderSum, remainder, Finset.sum_add_distrib, ← Finset.sum_div,
    retainedEnergy, rootQuartic]
  ring

/-- The actual retained cosine product, not a proxy, has this exact local logarithmic expansion. -/
theorem cosProduct_expansion (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) :
    cosProduct F x = Real.exp (-(x ⬝ᵥ rootMatrix F *ᵥ x)/2-rootQuartic F x+remainderSum F x) := by
  have hc (i j : Fin (n+1)) : 0 < Real.cos (rootLift x i-rootLift x j) :=
    cos_pos_of_abs_le_quarter (root_difference_quarter hr hrp hx i j)
  have he : cosProduct F x = Real.exp
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j), logCos (rootLift x i-rootLift x j)) := by
    unfold cosProduct
    simp only [Real.exp_sum, logCos, Real.exp_log (hc _ _)]
  rw [he, log_sum_identity, retainedEnergy_eq_root_quadratic]
end LocalLogCos
