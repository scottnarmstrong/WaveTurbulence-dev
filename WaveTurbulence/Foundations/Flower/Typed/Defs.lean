/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerFamily
public import WaveTurbulence.Foundations.Spine.TypeFamily
/-! # FL-TYPED definitions: frontier cutoffs, leaf products and the family pair profile. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Typed
open Finset

/-- Frontier (attachment-node) cutoffs, per-tree radius `Rf j` (`none`: no cutoff). -/
def frontierW {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (Rf : Fin w → Option ℝ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ a : GNode LG.garden.tree,
    if LG.IsTopLeaf p a ∧ LG.layer a < p ∧ ¬ LG.IsFlowerNode a then
      (Rf a.1.1).elim 1 fun r => chi0 (‖k a‖ / r) else 1

/-- Pair-type leaf profile product over the input leaves. -/
def leafProd {w d : ℕ} (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, LGSpine.typeProfiles LG h ℓ.1 (k ℓ.toNode)

/-- The pair profile of the family: `F q x * e_j(q,‖x‖) * e_{j'}(q,‖x‖)`. -/
def familyProfile {w d : ℕ} (F : ℕ → Mom d → ℝ) (p : ℕ) (M A : ℝ) (tail : Fin w → Bool)
    (z : Fin w → ℝ) (q : ℕ) (j j' : Fin w) (x : Mom d) : ℝ :=
  F q x * FC23.endpointFactor p q (tail j) M A (z j) ‖x‖ *
    FC23.endpointFactor p q (tail j') M A (z j') ‖x‖

end WaveTurbulence.Flower.Typed
