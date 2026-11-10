/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Garden
/-! # A2 CAPS-ID: caps and originals are equinumerous in every pairing-closed set of capped trees

`J.card = R` for a capped component of width `2R` (B0 finding F-B0-1): in a set `A` of capped trees whose leaves are
completely paired, the cap of tree `j` lies in `A` iff tree `j` does (the flower of `j` is paired with its cap).
Hence `#(caps in A) = #(originals in A) = |A| / 2` (`card_caps_eq_half`). Globally `(capJ w).card = w`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7

variable {w : ℕ}

theorem mem_capJ_iff (c : Fin (2 * w)) : c ∈ capJ w ↔ ∃ j, c = capσ w (.inr j) := by
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · simp only [capσ_inl_notMem_capJ, false_iff]
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr ((capσ w).injective hi)
  · exact iff_of_true (capσ_inr_mem_capJ j) ⟨j, rfl⟩

end WaveTurbulence.Flower.CapsId
