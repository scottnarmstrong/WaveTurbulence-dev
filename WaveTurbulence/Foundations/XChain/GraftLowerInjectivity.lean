/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GardenDataExt
public import WaveTurbulence.Foundations.XChain.GraftAddressInjectivity
public import WaveTurbulence.Foundations.XChain.GraftTreeRecovery
public import WaveTurbulence.Foundations.XChain.LayeredGraft
/-! Fixed top trees and their leaf partition uniquely determine every attached garden. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem gardenGraft_lower_injective {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → Garden B.1.card)
    (hl : ∀ B, (low B).IsPlain) (hh : ∀ B, (high B).IsPlain)
    (hsl : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hsh : ∀ B k, (high B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (he : gardenGraft sig top P low hl hsl = gardenGraft sig top P high hh hsh)
    (B : P.parts) : low B = high B := by
  apply garden_eq_of_raw_data
  · exact funext (fun k => (hsl B k).trans (hsh B k).symm)
  · exact funext (graftForest_injective_lower_trees top P low high (congrArg Garden.tree he) B)
  · intro a b hab
    have hp := garden_pair_raw_of_eq he
      ((gardenLeafEquiv top P low).symm ⟨B, a⟩)
      ((gardenLeafEquiv top P high).symm ⟨B, b⟩)
      (graft_lower_leaf_raw_congr top P low high B a b hab)
    have hpl := congrArg (fun l : GLeaf (gardenGraft sig top P low hl hsl).tree => l.1)
      (gardenGraft_pair_lower sig top P low hl hsl B a)
    have hph := congrArg (fun l : GLeaf (gardenGraft sig top P high hh hsh).tree => l.1)
      (gardenGraft_pair_lower sig top P high hh hsh B b)
    exact graft_lower_leaf_raw_injective top P low high B ((low B).pair a) ((high B).pair b)
      (hpl.symm.trans (hp.trans hph))
  · intro a b _
    exact (hl B a).trans (hh B b).symm

theorem layeredGardenGraft_lower_injective {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hl : ∀ B, (low B).garden.IsPlain) (hh : ∀ B, (high B).garden.IsPlain)
    (hsl : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hsh : ∀ B k, (high B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbl : ∀ B a, (low B).layer a ≤ p) (hbh : ∀ B a, (high B).layer a ≤ p)
    (he : layeredGardenGraft sig top P low p hl hsl hbl =
      layeredGardenGraft sig top P high p hh hsh hbh) (B : P.parts) : low B = high B := by
  apply layeredGarden_eq_of_raw_data
  · exact gardenGraft_lower_injective sig top P _ _ hl hh hsl hsh
      (congrArg LayeredGarden.garden he) B
  · intro a b hab
    have hraw := graft_lower_node_raw_congr top P
      (fun B => (low B).garden) (fun B => (high B).garden) B a b hab
    have hn := layeredGarden_layer_raw_of_eq he
      (gardenNodeEquiv top P (fun B => (low B).garden) (.inr ⟨B, a⟩))
      (gardenNodeEquiv top P (fun B => (high B).garden) (.inr ⟨B, b⟩))
      hraw
    exact (graftLayer_lower top P low p B a).symm.trans
      (hn.trans (graftLayer_lower top P high p B b))

end WaveTurbulence.Induct
