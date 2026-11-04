/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootGeometry

/-!
# Selecting complete linked pairs of vertex clocks

The fields are finite coordinate data only. Pair completeness proves
balance of the selected temporal frequencies and the two-link cardinality
bound used by the tree estimate.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- A clock permutation selecting both endpoints of every touched link. -/
structure SelectedLinkClocks (n r : ℕ) where
  coordinates : RootCoordinates n r
  pairing : Fin r ≃ ({i : Fin n // i ∈ coordinates.rootLinks} × Fin 2)
  vertex_eq : ∀ a, coordinates.rootVertex a = ((pairing a).1.val, (pairing a).2)

/-- Pair completeness determines the number of touched links exactly. -/
theorem SelectedLinkClocks.card_links_mul_two {n r : ℕ} (S : SelectedLinkClocks n r) :
    S.coordinates.rootLinks.card * 2 = r := by
  have h := Fintype.card_congr S.pairing
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe] using h.symm

/-- The two/four-clock cases touch at most two actual links. -/
theorem SelectedLinkClocks.card_links_le_two {n r : ℕ} (S : SelectedLinkClocks n r) (hr : r ≤ 4) :
    S.coordinates.rootLinks.card ≤ 2 := by
  have h := S.card_links_mul_two
  omega

/-- The selected frequency of an endpoint is the link frequency with its endpoint sign. -/
@[expose] def SelectedLinkClocks.phase {n r : ℕ} (S : SelectedLinkClocks n r)
    (Γ : Fin n → ℝ) (a : Fin r) : ℝ :=
  if (S.pairing a).2 = 0 then Γ (S.pairing a).1.val else -Γ (S.pairing a).1.val

/-- No phase-balance premise is assumed: it follows from selecting complete pairs. -/
theorem SelectedLinkClocks.phase_sum {n r : ℕ} (S : SelectedLinkClocks n r) (Γ : Fin n → ℝ) :
    ∑ a, S.phase Γ a = 0 := by
  classical
  unfold phase
  rw [S.pairing.sum_comp (fun p : {i : Fin n // i ∈ S.coordinates.rootLinks} × Fin 2 =>
    if p.2 = 0 then Γ p.1.val else -Γ p.1.val)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Reconstructing a selected endpoint reads exactly its paired selected clock. -/
theorem SelectedLinkClocks.equiv_symm_selected {n r : ℕ} (S : SelectedLinkClocks n r)
    (v : Fin r → ℝ) (u : Fin S.coordinates.restCount → ℝ)
    (i : {i : Fin n // i ∈ S.coordinates.rootLinks}) (j : Fin 2) :
    S.coordinates.equiv.symm (v, u) i.val j = v (S.pairing.symm (i, j)) := by
  have h := S.coordinates.equiv_symm_rootVertex v u (S.pairing.symm (i, j))
  rw [S.vertex_eq, S.pairing.apply_symm_apply] at h
  exact h

end WaveTurbulence.Incoh
