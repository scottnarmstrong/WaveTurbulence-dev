/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
public import WaveTurbulence.Foundations.XChain.GardenGraftOrder
public import WaveTurbulence.Foundations.XChain.TreeLeafCard
/-! A fully truncated construction has a finite explicit total-order bound. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem canonicalGraftData_order_le {w p : ℕ} {sig : Fin w → ℤˣ}
    (C : CanonicalGraftData sig p) (Ntop Natt : ℕ) (htr : C.IsTrunc Ntop Natt) :
    C.graft.garden.order ≤ w * Ntop + (2 * (w * Ntop) + w) * Natt := by
  have ht : (∑ j, (C.top j).order) ≤ w * Ntop := by
    simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using
      sum_le_sum (s := (univ : Finset (Fin w))) (fun j _ => htr.1 j)
  have hl : (∑ B : C.partition.parts, (C.low B).garden.order) ≤ C.partition.parts.card * Natt := by
    simpa only [sum_const, card_univ, Fintype.card_coe, smul_eq_mul] using
      sum_le_sum (s := (univ : Finset C.partition.parts)) (fun B _ => htr.2 B)
  have hp : C.partition.parts.card ≤ 2 * (w * Ntop) + w := by
    have hc := C.partition.card_parts_le_card
    simp only [card_univ, forest_card_leaves_eq] at hc
    exact hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ht) w)
  have ho := gardenGraft_order sig C.top C.partition (fun B => (C.low B).garden) C.plain C.sign
  exact ho.trans_le ((Nat.add_le_add ht hl).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right Natt hp) (w * Ntop)))

end WaveTurbulence.Induct
