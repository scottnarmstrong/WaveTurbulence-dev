/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedLinkClocks
public import WaveTurbulence.Foundations.Fourier.BalancedPhase

/-!
# The selected vertex phase is the product of the actual link phases

Pair completeness supplies the phase identity, without an assumed
oscillatory representation or a balance hypothesis.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Group the signed vertex frequencies into the differences on each actual link. -/
theorem SelectedLinkClocks.phase_dot {n r : ℕ} (S : SelectedLinkClocks n r)
    (Γ : Fin n → ℝ) (v : Fin r → ℝ) :
    ∑ a, S.phase Γ a * v a =
      ∑ i : {i : Fin n // i ∈ S.coordinates.rootLinks},
        Γ i.val * (v (S.pairing.symm (i, 0)) - v (S.pairing.symm (i, 1))) := by
  classical
  have h := S.pairing.sum_comp (fun p : {i : Fin n // i ∈ S.coordinates.rootLinks} × Fin 2 =>
    (if p.2 = 0 then Γ p.1.val else -Γ p.1.val) * v (S.pairing.symm p))
  simpa [SelectedLinkClocks.phase, Fintype.sum_prod_type, Fin.sum_univ_two, mul_sub, sub_eq_add_neg, mul_add, Finset.sum_add_distrib] using h

/-- The literal balanced linear phase factors over the selected links. -/
theorem SelectedLinkClocks.linearTimePhase_eq_prod {n r : ℕ} (S : SelectedLinkClocks n r)
    (Γ : Fin n → ℝ) (v : Fin r → ℝ) :
    Fourier.linearTimePhase (S.phase Γ) v =
      ∏ i : {i : Fin n // i ∈ S.coordinates.rootLinks},
        Complex.exp ((Γ i.val *
          (v (S.pairing.symm (i, 0)) - v (S.pairing.symm (i, 1))) : ℝ) * Complex.I) := by
  unfold Fourier.linearTimePhase
  rw [S.phase_dot]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- In reconstructed vertex coordinates these are precisely the link time differences. -/
theorem SelectedLinkClocks.linearTimePhase_eq_link_prod {n r : ℕ}
    (S : SelectedLinkClocks n r) (Γ : Fin n → ℝ)
    (v : Fin r → ℝ) (u : Fin S.coordinates.restCount → ℝ) :
    Fourier.linearTimePhase (S.phase Γ) v =
      ∏ i : {i : Fin n // i ∈ S.coordinates.rootLinks},
        Complex.exp ((Γ i.val *
          (S.coordinates.equiv.symm (v, u) i.val 0 -
            S.coordinates.equiv.symm (v, u) i.val 1) : ℝ) * Complex.I) := by
  simp only [S.equiv_symm_selected]
  exact S.linearTimePhase_eq_prod Γ v

end WaveTurbulence.Incoh
