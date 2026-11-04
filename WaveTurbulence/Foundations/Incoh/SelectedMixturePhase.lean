/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedClockPhase
public import WaveTurbulence.Foundations.Incoh.ExpandedLinkFactor

/-!
# The actual selected mixture phases equal the balanced vertex phase

Unused lattice phase coordinates contribute one. Complete linked-pair
selection identifies the remaining product exactly, before integration.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Restore the literal selected lattice phases in their selected vertex coordinates. -/
theorem SelectedLinkClocks.prod_linkMixturePhase {d n r : ℕ} (S : SelectedLinkClocks n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (v : Fin r → ℝ) (u : Fin S.coordinates.restCount → ℝ) :
    (∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ S.coordinates.rootLinks))
      (p i, S.coordinates.equiv.symm (v, u) i)) =
      Fourier.linearTimePhase (S.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i))) v := by
  classical
  rw [S.linearTimePhase_eq_link_prod _ v u]
  rw [Finset.prod_coe_sort S.coordinates.rootLinks (fun i =>
    Complex.exp ((linkTemporalFrequency L γ δ (Q i) (p i) *
      (S.coordinates.equiv.symm (v, u) i 0 - S.coordinates.equiv.symm (v, u) i 1) : ℝ) * Complex.I))]
  simp only [linkMixturePhase, decide_eq_true_eq]
  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

end WaveTurbulence.Incoh
