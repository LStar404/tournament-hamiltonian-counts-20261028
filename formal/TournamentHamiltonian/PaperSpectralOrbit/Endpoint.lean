module
public import TournamentHamiltonian.Equality.SpectralClassification
public import TournamentHamiltonian.Equality.SignedPermutationMatrix
@[expose] public section
set_option autoImplicit false
namespace PaperSpectralOrbit
open TournamentHamiltonian TournamentHamiltonian.Equality

theorem signedPermutationMatrix_transpose {n : ℕ} (ε : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    (signedPermutationMatrix ε e).transpose =
      signedPermutationMatrix (fun i => ε (e i)) e.symm := by
  ext i j
  simp only [Matrix.transpose_apply, signedPermutationMatrix_apply]
  by_cases h : j=e i
  · subst j
    simp
  · have h' : i ≠ e.symm j := by
      intro hi
      apply h
      rw [hi,Equiv.apply_symm_apply]
    simp [h,h']

theorem reverse_signed_conjugation {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n))
    (hε : ∀ i, ε i=1 ∨ ε i= -1)
    (h : (signedPermutationMatrix ε e).transpose*A*signedPermutationMatrix ε e=B) :
    (signedPermutationMatrix (fun i => ε (e i)) e.symm).transpose * B *
      signedPermutationMatrix (fun i => ε (e i)) e.symm = A := by
  let Q := signedPermutationMatrix ε e
  have hsq (i : Fin n) : ε i^2=1 := by rcases hε i with h|h <;> rw [h] <;> norm_num
  have hqt : Q.transpose*Q=1 := signedPermutationMatrix_orthogonal ε hsq e
  have hqq : Q*Q.transpose=1 := mul_eq_one_comm.mp hqt
  rw [← signedPermutationMatrix_transpose,Matrix.transpose_transpose,←h]
  change Q*(Q.transpose*A*Q)*Q.transpose=A
  calc
    Q*(Q.transpose*A*Q)*Q.transpose=(Q*Q.transpose)*A*(Q*Q.transpose) := by noncomm_ring
    _ = A := by rw [hqq]; simp

theorem signed_class_iff_paper_conjugation {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    SignedPermutationTransitive S ↔
      ∃ (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n)),
        (∀ i,ε i=1 ∨ ε i= -1) ∧
        (signedPermutationMatrix ε e).transpose *
          (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) * signedPermutationMatrix ε e=S := by
  constructor
  · rintro ⟨ε,hε,e,he⟩
    refine ⟨(fun i => ε (e i)),e.symm,(fun i => hε (e i)),?_⟩
    apply reverse_signed_conjugation S (transitiveSkew n) ε e hε
    rw [signedPermutationMatrix_conjugation,he]
  · rintro ⟨ε,e,hε,he⟩
    refine ⟨(fun i => ε (e i)),(fun i => hε (e i)),e.symm,?_⟩
    rw [← signedPermutationMatrix_conjugation]
    exact reverse_signed_conjugation (transitiveSkew n) S ε e hε he

/-- Literal upper bound and the paper's displayed conjugation direction.
This is a derived endpoint bridge; no prior source is edited. -/
theorem paper_6_4 {n : ℕ} (T : Tournament n) :
    spectralRatio T ≤ spectralRatio (alternatingTournament n) ∧
      (spectralRatio T=spectralRatio (alternatingTournament n) ↔
        ∃ (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n)),
          (∀ i,ε i=1 ∨ ε i= -1) ∧
          (signedPermutationMatrix ε e).transpose *
            (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) *
              signedPermutationMatrix ε e=signMatrix T) := by
  constructor
  · by_cases h : SignedPermutationTransitive (signMatrix T)
    · exact ((spectralRatio_eq_iff_signedPermutationTransitive T).mpr h).le
    · exact ((spectralRatio_lt_iff_not_signedPermutationTransitive T).mpr h).le
  · rw [spectralRatio_eq_iff_signedPermutationTransitive,signed_class_iff_paper_conjugation]

end PaperSpectralOrbit
