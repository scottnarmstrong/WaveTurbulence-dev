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

/-- The original-tree embedding `j ↦ capσ w (inl j)`. -/
def inlEmb (w : ℕ) : Fin w ↪ Fin (2 * w) := ⟨fun j => capσ w (.inl j), fun _ _ h => Sum.inl_injective ((capσ w).injective h)⟩

/-- The cap embedding `j ↦ capσ w (inr j)`. -/
def inrEmb (w : ℕ) : Fin w ↪ Fin (2 * w) := ⟨fun j => capσ w (.inr j), fun _ _ h => Sum.inr_injective ((capσ w).injective h)⟩

theorem mem_capJ_iff (c : Fin (2 * w)) : c ∈ capJ w ↔ ∃ j, c = capσ w (.inr j) := by
  obtain ⟨s, rfl⟩ := (capσ w).surjective c
  rcases s with j | j
  · simp only [capσ_inl_notMem_capJ, false_iff]
    rintro ⟨i, hi⟩
    exact Sum.inl_ne_inr ((capσ w).injective hi)
  · exact iff_of_true (capσ_inr_mem_capJ j) ⟨j, rfl⟩

/-- The capped garden has `w` caps. -/
theorem card_capJ (w : ℕ) : (capJ w).card = w := by
  have : capJ w = Finset.univ.map (inrEmb w) := by
    ext c
    rw [mem_capJ_iff, Finset.mem_map]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, Finset.mem_univ _, rfl⟩
    · rintro ⟨j, -, rfl⟩; exact ⟨j, rfl⟩
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- In a pairing-closed set of capped trees, a cap is present iff its original tree is. -/
theorem inl_mem_iff_inr_mem (G : Garden w) (hF : OneFlower G) (A : Finset (Fin (2 * w)))
    (hA : (capGarden G).CompletelyPaired ((capGarden G).leavesOf A)) (j : Fin w) :
    capσ w (.inl j) ∈ A ↔ capσ w (.inr j) ∈ A := by
  obtain ⟨ℓ, hℓ⟩ := flowerOf_isSome hF j
  obtain ⟨hj, hfl⟩ := flowerOf_spec hℓ
  constructor
  · intro h
    have hm : embL G ℓ ∈ (capGarden G).leavesOf A := by
      simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and, embL_val, hj]
      exact h
    have hp := (hA _ hm).2
    rw [capGarden_pair_flower G hF hfl] at hp
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and, capL_val, hj] at hp
    exact hp
  · intro h
    have hm : capL G j ∈ (capGarden G).leavesOf A := by
      simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and, capL_val]
      exact h
    have hp := (hA _ hm).2
    rw [capGarden_pair_capL_of G hℓ] at hp
    simp only [Garden.leavesOf, Finset.mem_filter, Finset.mem_univ, true_and, embL_val, hj] at hp
    exact hp

/-- **Caps and originals are equinumerous** in a pairing-closed set of capped trees. -/
theorem card_caps_eq_card_originals (G : Garden w) (hF : OneFlower G) (A : Finset (Fin (2 * w)))
    (hA : (capGarden G).CompletelyPaired ((capGarden G).leavesOf A)) :
    (A.filter (· ∈ capJ w)).card = (A.filter (· ∉ capJ w)).card := by
  have h1 : A.filter (· ∈ capJ w) = (Finset.univ.filter fun j => capσ w (.inl j) ∈ A).map (inrEmb w) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, mem_capJ_iff]
    constructor
    · rintro ⟨hc, j, rfl⟩
      exact ⟨j, (inl_mem_iff_inr_mem G hF A hA j).2 hc, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(inl_mem_iff_inr_mem G hF A hA j).1 hj, j, rfl⟩
  have h2 : A.filter (· ∉ capJ w) = (Finset.univ.filter fun j => capσ w (.inl j) ∈ A).map (inlEmb w) := by
    ext c
    obtain ⟨s, rfl⟩ := (capσ w).surjective c
    rcases s with j | j
    · simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, capσ_inl_notMem_capJ,
        not_false_eq_true, and_true, inlEmb]
      constructor
      · intro h; exact ⟨j, h, rfl⟩
      · rintro ⟨i, hi, he⟩
        rw [← Sum.inl_injective ((capσ w).injective he)]; exact hi
    · simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, capσ_inr_mem_capJ,
        not_true_eq_false, and_false, false_iff, inlEmb]
      rintro ⟨i, -, he⟩
      exact Sum.inl_ne_inr ((capσ w).injective he)
  rw [h1, h2, Finset.card_map, Finset.card_map]

/-- **`J.card = R` per capped component**: a pairing-closed set of `2R` capped trees contains exactly `R` caps. -/
theorem card_caps_eq_half (G : Garden w) (hF : OneFlower G) (A : Finset (Fin (2 * w)))
    (hA : (capGarden G).CompletelyPaired ((capGarden G).leavesOf A)) {R : ℕ} (hR : A.card = 2 * R) :
    (A.filter (· ∈ capJ w)).card = R := by
  have h := card_caps_eq_card_originals G hF A hA
  have hs := Finset.card_filter_add_card_filter_not (s := A) (fun c => c ∈ capJ w)
  omega

end WaveTurbulence.Flower.CapsId
