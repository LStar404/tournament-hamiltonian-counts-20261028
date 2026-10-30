module

public import TournamentHamiltonian.NonregularNormalization.FineStirling

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace StrictStirling
open Filter
open scoped Topology BigOperators

/-- Strict positivity uses the positive j=0 term of the actual log-step series. -/
lemma log_step_pos (k : ℕ) :
    0 < Real.log (Stirling.stirlingSeq (k+1))-Real.log (Stirling.stirlingSeq (k+2)) := by
  have hs := Stirling.log_stirlingSeq_sdiff_hasSum k
  exact hasSum_lt (fun j => by positivity) (by positivity : (0:ℝ) <
    (1:ℝ)/(2*((0+1:ℕ):ℝ)+1)*((1/(2*((k+1:ℕ):ℝ)+1))^2)^(0+1:ℕ))
    hasSum_zero hs

/-- Strict Robbins step: j=0 attains the comparison, but j=1 is strictly smaller. -/
lemma log_step_lt (k : ℕ) :
    Real.log (Stirling.stirlingSeq (k+1))-Real.log (Stirling.stirlingSeq (k+2)) <
      1/(12*((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1)) := by
  let r : ℝ := ((1:ℝ)/(2*((k+1:ℕ):ℝ)+1))^2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    have hd : (1:ℝ)/(2*((k+1:ℕ):ℝ)+1) < 1 := by
      apply (div_lt_one (by positivity)).mpr
      have hk : (0:ℝ) < ((k+1:ℕ):ℝ) := by positivity
      linarith
    have hd0 : 0 ≤ (1:ℝ)/(2*((k+1:ℕ):ℝ)+1) := by positivity
    dsimp [r]
    nlinarith
  have hg : HasSum (fun j : ℕ => r^(j+1)/3)
      ((1:ℝ)/(12*((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1))) := by
    have h := ((hasSum_geometric_of_lt_one hr0.le hr1).mul_right r).div_const 3
    convert h using 1
    · ext j
      rw [pow_succ]
    · have hid : 1-r = 4*((k+1:ℕ):ℝ)*(((k+1:ℕ):ℝ)+1)/(2*((k+1:ℕ):ℝ)+1)^2 := by
        dsimp [r]
        field_simp
        ring
      rw [hid, inv_div]
      dsimp [r]
      field_simp
      ring
  have hs := Stirling.log_stirlingSeq_sdiff_hasSum k
  apply hasSum_lt (i := 1) _ _ hs hg
  · intro j
    change (1:ℝ)/(2*((j+1:ℕ):ℝ)+1)*r^(j+1) ≤ r^(j+1)/3
    have hj : (3:ℝ) ≤ 2*((j+1:ℕ):ℝ)+1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hi : (1:ℝ)/(2*((j+1:ℕ):ℝ)+1) ≤ 1/3 := by
      exact one_div_le_one_div_of_le (by norm_num) hj
    nlinarith [mul_le_mul_of_nonneg_right hi (pow_nonneg hr0.le (j+1))]
  · change (1:ℝ)/(2*((1+1:ℕ):ℝ)+1)*r^(1+1) < r^(1+1)/3
    norm_num
    nlinarith [sq_pos_of_pos hr0]

/-- Both strict global log-sequence inequalities use only one strict step and
already-frozen non-strict bounds at the next index. -/
lemma log_sequence_strict (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Real.sqrt Real.pi) < Real.log (Stirling.stirlingSeq n) ∧
    Real.log (Stirling.stirlingSeq n) < Real.log (Real.sqrt Real.pi)+1/(12*(n:ℝ)) := by
  have hp := log_step_pos (n-1)
  have hu := log_step_lt (n-1)
  have hn1 : n-1+1=n := Nat.sub_add_cancel hn
  have hn2 : n-1+2=n+1 := by omega
  rw [hn1,hn2] at hp hu
  have hlo : Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq (n+1)) :=
    Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero n))
  have hhi := NonregularNormalization.log_stirlingSeq_le_robbins (n := n+1) (by omega)
  have hnR : (n:ℝ)≠0 := by positivity
  have he : 1/(12*(n:ℝ)) = 1/(12*((n+1:ℕ):ℝ)) + 1/(12*(n:ℝ)*((n:ℝ)+1)) := by
    push_cast
    field_simp
  constructor
  · linarith
  · rw [he]
    linarith

/-- The actual factorial has a strictly positive remainder strictly below 1/(12n). -/
theorem log_factorial_strict (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2 < Real.log (n.factorial:ℝ) ∧
    Real.log (n.factorial:ℝ) <
      (n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2+1/(12*(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h := log_sequence_strict n hn
  rw [Stirling.log_stirlingSeq_formula] at h
  rw [Real.log_div hnR.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2:ℝ)≠0) hnR.ne', Real.log_sqrt Real.pi_pos.le] at h
  rw [Real.log_mul (by positivity : 2*Real.pi≠0) hnR.ne',
    Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_pos.ne']
  constructor <;> linarith [h.1,h.2]

/-- An explicit remainder coefficient, not an unspecified witness. -/
def theta (n : ℕ) : ℝ := 12*(n:ℝ)*
  (Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2))

theorem theta_bounds (n : ℕ) (hn : 1 ≤ n) : 0 < theta n ∧ theta n < 1 := by
  have h := log_factorial_strict n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  unfold theta
  constructor
  · exact mul_pos (by positivity) (sub_pos.mpr h.1)
  · have hp : 0 < 12*(n:ℝ) := by positivity
    have hh := (lt_div_iff₀ hp).mp (show Real.log (n.factorial:ℝ)-
      ((n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2) < 1/(12*(n:ℝ)) by linarith [h.2])
    nlinarith

theorem log_factorial_eq (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial:ℝ) = (n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2+theta n/(12*(n:ℝ)) := by
  have hnR : (n:ℝ)≠0 := by positivity
  unfold theta
  field_simp
  ring

/-- The same explicit coefficient in the actual factorial, multiplicative form. -/
theorem factorial_eq (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial:ℝ) = Real.sqrt (2*Real.pi*n)*((n:ℝ)/Real.exp 1)^n*
      Real.exp (theta n/(12*(n:ℝ))) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  rw [log_factorial_eq n hn,
    Real.log_mul (by positivity : Real.sqrt (2*Real.pi*n)*((n:ℝ)/Real.exp 1)^n≠0) (Real.exp_pos _).ne',
    Real.log_mul (by positivity : Real.sqrt (2*Real.pi*n)≠0) (by positivity : ((n:ℝ)/Real.exp 1)^n≠0),
    Real.log_sqrt (by positivity), Real.log_pow,
    Real.log_div hnR.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_exp]
  ring

/-- Literal §11.5 statement, for every integer R≥1 and with 0<θ_R<1. -/
theorem exists_strict_remainder (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, 0<θ ∧ θ<1 ∧ Real.log (n.factorial:ℝ) =
      (n:ℝ)*Real.log n-n+Real.log (2*Real.pi*n)/2+θ/(12*(n:ℝ)) :=
  ⟨theta n,(theta_bounds n hn).1,(theta_bounds n hn).2,log_factorial_eq n hn⟩

end StrictStirling
