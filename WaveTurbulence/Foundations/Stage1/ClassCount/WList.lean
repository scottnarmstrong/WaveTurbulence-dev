/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCode2
import Mathlib.Tactic

/-!
# CLASSCOUNT: weighted lists

`wlists F W` is the finite set of lists `x_1 :: ⋯ :: x_m` with `x_j ∈ F (w_j)`, `w_j ≥ 1`, `Σ w_j = W`.  If
`|F w| ≤ c^w` for `w ≥ 1`, then `|wlists F W| ≤ (2c)^W` (`card_wlists_le`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

variable {α : Type*} [DecidableEq α]

/-- Lists of weighted elements of total weight `W`. -/
noncomputable def wlists (F : ℕ → Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | W + 1 => (Finset.range (W + 1)).attach.biUnion (fun i =>
      ((F (i.1 + 1)) ×ˢ wlists F (W - i.1)).image (fun p => p.1 :: p.2))
termination_by W => W
decreasing_by omega

theorem mem_wlists_cons (F : ℕ → Finset α) {x : α} {xs : List α} {w W : ℕ} (hw : 1 ≤ w)
    (hx : x ∈ F w) (hxs : xs ∈ wlists F W) : x :: xs ∈ wlists F (w + W) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [show w' + 1 + W = (w' + W) + 1 by omega, wlists]
  refine Finset.mem_biUnion.mpr ⟨⟨w', Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _, ?_⟩
  refine Finset.mem_image.mpr ⟨(x, xs), Finset.mem_product.mpr ⟨hx, ?_⟩, rfl⟩
  have : (w' + W) - w' = W := by omega
  simp only
  rw [this]; exact hxs

theorem nil_mem_wlists (F : ℕ → Finset α) : ([] : List α) ∈ wlists F 0 := by simp [wlists]

theorem card_wlists_le (F : ℕ → Finset α) (c : ℕ) (hF : ∀ w, 1 ≤ w → (F w).card ≤ c ^ w) :
    ∀ W : ℕ, (wlists F W).card ≤ (2 * c) ^ W
  | 0 => by simp [wlists]
  | W + 1 => by
    rw [wlists]
    refine Finset.card_biUnion_le.trans ?_
    have hterm : ∀ i : {x // x ∈ Finset.range (W + 1)},
        (((F (i.1 + 1)) ×ˢ wlists F (W - i.1)).image (fun p => p.1 :: p.2)).card ≤
          c ^ (i.1 + 1) * (2 * c) ^ (W - i.1) := by
      intro i
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul (hF _ (by omega)) (card_wlists_le F c hF (W - i.1))
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    rw [Finset.sum_attach (Finset.range (W + 1)) (fun i => c ^ (i + 1) * (2 * c) ^ (W - i))]
    exact geom_sum_bound c W

end WaveTurbulence.ClassCount
