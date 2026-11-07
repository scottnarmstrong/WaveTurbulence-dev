/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Coh1
import Mathlib.Tactic

/-!
# Native layer counts depend only on the layers at the native branch addresses
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ} {S : Garden w}

theorem rawTreeLayerCount_eq (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ)
    (b : GBranch S.tree) :
    rawTreeLayerCount LG D hS p b =
      ((((D.tree b).plug (nodeSign S.sig b.1) .leaf).branching).filter
        (fun q => layerAt LG (addrExt (inflatedPosition S D.tree b.toNode) q) = p)).card := by
  classical
  unfold rawTreeLayerCount
  rw [Finset.card_filter]
  exact Finset.sum_coe_sort (((D.tree b).plug (nodeSign S.sig b.1) .leaf).branching)
    (fun q => if layerAt LG (addrExt (inflatedPosition S D.tree b.toNode) q) = p then 1 else 0)

/-- The count over the branches of a decoded couple, for a layer function given on relative addresses. -/
@[expose] noncomputable def coupleSum (Q : RegCpl) (F : Fin 2 → Path → ℕ) (p : ℕ) : ℕ := by
  classical
  exact ∑ c : GBranch (decodedCouple Q).tree, if F c.1.1 c.1.2 = p then 1 else 0

theorem rawCoupleLayerCount_eq (LG : LayeredGarden w) (D : ReconstructionData S) (hS : S.IsPlain) (p : ℕ)
    (q : SourcePair S) :
    rawCoupleLayerCount LG D hS p q =
      coupleSum (D.couple q) (fun j r => layerAt LG (addrExt (coupleRoot D hS q j) r)) p := by
  classical
  unfold rawCoupleLayerCount coupleSum
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h : (coupleContextBranch D hS q c).1 = addrExt (coupleRoot D hS q c.1.1) c.1.2 := by
    rcases c with ⟨⟨j, r⟩, hc⟩
    fin_cases j <;> rfl
  simp only [h]

theorem coupleSum_congr (Q : RegCpl) (F G : Fin 2 → Path → ℕ) (p : ℕ)
    (h : ∀ j r, r ∈ (coupleForest Q j).branching → F j r = G j r) :
    coupleSum Q F p = coupleSum Q G p := by
  classical
  unfold coupleSum
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [h c.1.1 c.1.2 c.2]

end WaveTurbulence.Stage1
