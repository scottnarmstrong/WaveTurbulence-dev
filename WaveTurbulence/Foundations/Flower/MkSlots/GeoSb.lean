/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Slice
public import WaveTurbulence.Foundations.Flower.MkSlots.Geo
public import WaveTurbulence.Foundations.Flower.MkMark.Owner
public import WaveTurbulence.Foundations.Vine.B.Fold7

/-! # B3s MK-SLOTS: the pins of a class piece on `G_sb` are admissible (milestone α)

* `ob_fst`, `coreOf_fst`: a branch of `G_sb`, its old name in the skeleton and its core branch in the layered garden
  lie in the same tree (main's fold invariant `FoldInv.tree_eq`/`br_node`, B2b's `inflatedPosition_fst`).
* `admissibleSb_plain`: with plain patterns, the pins `fixOf` of the piece of `a` (capped flower parents at
  `s ∈ (p, t)`) are admissible for the spliced domain with layers `coreOf`-layers and root time `t`: values in the
  layer window `[p, p+1]` and below `t`; pinned atoms in pairwise distinct trees (one capped flower per tree). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 unitBlocks)

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- A branch of `G_sb` and its old name lie in the same tree. -/
theorem ob_fst (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) :
    ((stA mkF a).M.ob c).1.1 = c.1.1 := by
  have hF := VineB.spliceFoldInv a.prime.skeleton (unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a))
    (RedSplice.unitBlocks_pairwiseMk (Mole.garden_isMolecule _) _ _)
  have h1 := congrArg (fun x : GNode a.prime.skeleton.tree => x.1.1) (hF.br_node c)
  exact h1.trans (hF.tree_eq c.toNode)

/-- A branch of `G_sb` and its core branch lie in the same tree. -/
theorem coreOf_fst (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) :
    (coreOf mkF a c).1.1 = c.1.1 := by
  show (a.prime.data.corePosition ((stA mkF a).M.ob c)).1 = c.1.1
  unfold ReconstructionData.corePosition
  show (inflatedPosition a.prime.skeleton a.prime.data.tree ((stA mkF a).M.ob c).toNode).1 = c.1.1
  rw [MkMark.inflatedPosition_fst]
  exact ob_fst mkF a c

end WaveTurbulence.Flower.MkSlots
