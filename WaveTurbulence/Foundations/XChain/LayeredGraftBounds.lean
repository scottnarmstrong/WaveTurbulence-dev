/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayeredGraft
/-! Uniform layer and parent-layer bounds for the actual graft. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem parentLayer_le_of_layer_le {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (h : ∀ a, LG.layer a ≤ p) (a : GNode LG.garden.tree) : LG.parentLayer p a ≤ p := by
  unfold LayeredGarden.parentLayer
  split_ifs
  · exact le_refl p
  · exact h _

theorem graftLayer_le {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (hbound : ∀ B a, (low B).layer a ≤ p)
    (a : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden)))) :
    graftLayer top P low p a ≤ p := by
  obtain ⟨z, rfl⟩ := (gardenNodeEquiv top P (fun B => (low B).garden)).surjective a
  rcases z with b | ⟨B, a⟩
  · exact (graftLayer_top top P low p b).le
  · rw [graftLayer_lower]
    exact hbound B a

end WaveTurbulence.Induct
