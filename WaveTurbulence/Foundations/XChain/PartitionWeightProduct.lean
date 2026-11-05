/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! The block weights in cmattr are exactly one weight per top leaf. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem prod_finpartition_blocks {α M : Type*} [DecidableEq α] [CommMonoid M]
    {s : Finset α} (P : Finpartition s) (f : α → M) :
    (∏ B : P.parts, ∏ a ∈ B.1, f a) = ∏ a ∈ s, f a := by
  classical
  rw [prod_coe_sort P.parts (fun B => ∏ a ∈ B, f a)]
  have he := prod_biUnion (f := f) P.supIndep.pairwiseDisjoint
  rw [P.biUnion_parts] at he
  exact he.symm

theorem prod_finpartition_rpow {α : Type*} [DecidableEq α]
    {s : Finset α} (P : Finpartition s) (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a)
    (C b : ℝ) :
    (∏ B : P.parts, C * (∏ a ∈ B.1, f a) ^ b) =
      C ^ P.parts.card * (∏ a ∈ s, f a) ^ b := by
  classical
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe]
  congr 1
  have hn (B : P.parts) : 0 ≤ ∏ a ∈ B.1, f a :=
    prod_nonneg (fun a ha => hf a (P.le B.2 ha))
  rw [Real.finsetProd_rpow (univ : Finset P.parts) (fun B : P.parts => ∏ a ∈ B.1, f a) (fun B _ => hn B), prod_finpartition_blocks]

end WaveTurbulence.Induct
