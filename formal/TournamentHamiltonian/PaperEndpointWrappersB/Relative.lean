module

public import TournamentHamiltonian.PaperEndpointWrappersB.SmallScore

@[expose] public section

/-! Audited literal relative-error extraction for manuscript Lemma 4.5.
The frozen four-source B package is not modified. -/
set_option autoImplicit false
noncomputable section
namespace PaperEndpointWrappersB
open TournamentHamiltonian

theorem relative_main_term_pos {n : ℕ} (T : Tournament n) (hn : 0<n) (t : ℕ) :
    0 < Real.exp (-1) * gaussianFactor T * (((n-t).factorial : ℝ) / (2:ℝ)^(n-t)) := by
  have hG := (gaussianFactor_bounds T hn).1
  positivity

theorem relative_error_of_absolute {p a e : ℝ} (ha : 0<a) (h : |p-a| ≤ a*e) :
    |p/a-1| ≤ e := by
  have he : p/a-1=(p-a)/a := by field_simp
  rw [he,abs_div,abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using h)

/-- Literal relative-error form, with the same quantifier order as manuscript 4.5. -/
theorem lemma4_5_relative_actual_score (B : ℝ) (hB : 0<B) :
    ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∃ N : ℕ, 4≤N ∧
    ∀ n t : ℕ, N≤n → ∀ T : Tournament n,
      (t:ℝ)≤B*Real.log (n:ℝ) → (‖score T‖+(t:ℝ)+1)^2/n≤δ →
      ∀ I J : Finset (Fin n), ∀ hI : I.card=t, ∀ hJ : J.card=t,
      |rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
          (deletedComplementEquiv I J (hI.trans hJ.symm)) /
        (Real.exp (-1)*gaussianFactor T*(((n-t).factorial:ℝ)/(2:ℝ)^(n-t))) - 1| ≤
          C*((‖score T‖+(t:ℝ)+1)^2/n) := by
  obtain ⟨C,δ,hC,hδ,N,hN,h⟩ := lemma4_5_actual_score B hB
  refine ⟨C,δ,hC,hδ,N,hN,?_⟩
  intro n t hn T ht he I J hI hJ
  exact relative_error_of_absolute (relative_main_term_pos T (by omega) t) (h n t hn T ht he I J hI hJ)

end PaperEndpointWrappersB
