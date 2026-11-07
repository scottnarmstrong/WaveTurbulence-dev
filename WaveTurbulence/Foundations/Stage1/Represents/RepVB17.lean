/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB16
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-E: the order bookkeeping `hexp` of `representsIntA_of_vineModes`

`exponent_order`: `n - |G_sb| = Σ_{outer slots} slotSize + Σ_j clLocalOrder2` from `n - |S| = D.size`
(`|S| = |G_sb| + Σ_j clLocalOrder1`, VINE-B♯'s `order_split`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB
  WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem sum_slots_split (hS : S.IsPlain) (hd : Disj blk) (f : ReplacementSlot S → ℕ) :
    ∑ s, f s = (∑ s ∈ outerSlots blk hS, f s) + ∑ j, ∑ s ∈ regSlots blk hS j, f s := by
  have := prod_slots (blk := blk) hS hd (M := Multiplicative ℕ) (fun s => Multiplicative.ofAdd (f s))
  have h2 := congrArg Multiplicative.toAdd this
  simpa [toAdd_prod] using h2

theorem sum_regSlots_eq (hS : S.IsPlain) (j : J) (f : ReplacementSlot S → ℕ) :
    ∑ s ∈ regSlots blk hS j, f s =
      (∑ p ∈ clRegionalPairs hS (blk j).atoms, f (Sum.inl p)) + ∑ v ∈ inter blk j, f (Sum.inr v) := by
  have := prod_regSlots (blk := blk) hS j (M := Multiplicative ℕ) (fun s => Multiplicative.ofAdd (f s))
  have h2 := congrArg Multiplicative.toAdd this
  simpa [toAdd_prod] using h2

theorem sum_outer_iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) (f : ReplacementSlot S → ℕ) :
    ∑ s ∈ outerSlots blk hS, f s = ∑ s', f (Φ.iota hS hSb s') := by
  have := Φ.prod_outer_iota hS hSb (M := Multiplicative ℕ) (fun s => Multiplicative.ofAdd (f s))
  have h2 := congrArg Multiplicative.toAdd this
  simpa [toAdd_prod] using h2

theorem exponent_order (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (n : ℕ)
    (hn : n - S.order = D.size) (hnS : S.order ≤ n) :
    (∑ s', slotSize D (Φ.iota hS hSb s')) + ∑ j, clLocalOrder2 D hS (regionOf (blk j)) = n - Gsb.order := by
  have ho := Φ.order_split hd
  have hsz := sum_slotSize D
  rw [sum_slots_split hS hd (slotSize D), sum_outer_iota Φ hS hSb] at hsz
  have hreg : ∀ j, ∑ s ∈ regSlots blk hS j, slotSize D s + clLocalOrder1 (regionOf (blk j)) =
      clLocalOrder2 D hS (regionOf (blk j)) := by
    intro j
    rw [sum_regSlots_eq hS j]
    unfold clLocalOrder2 slotSize
    simp only [inter]
    ring
  have hsum : ∑ j, clLocalOrder2 D hS (regionOf (blk j)) =
      (∑ j, ∑ s ∈ regSlots blk hS j, slotSize D s) + ∑ j, clLocalOrder1 (regionOf (blk j)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (hreg j).symm
  omega

theorem card_hinges (hd : Disj blk) : (Φ.hinges hd).card = Fintype.card J := by
  unfold SpliceShape.hinges
  rw [Finset.card_image_of_injective _ (Φ.hinge_inj hd), Finset.card_univ]

include Φ in
theorem card_units_le_order (hd : Disj blk) : Fintype.card J ≤ Gsb.order := by
  rw [Garden.order, ← WaveTurbulence.Mole.card_gbranch]
  exact Fintype.card_le_of_injective _ (Φ.hinge_inj hd)

end WaveTurbulence.Represents
