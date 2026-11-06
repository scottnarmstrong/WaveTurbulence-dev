/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceChainBlocks
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedPairedTree

/-! # The actual source paired-tree carrier has exactly its chain context shape -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem embeddedPairedTree_shape_of_chain {w : ℕ} (X : RegChain) (ζ : ℤˣ) (G : Garden w)
    (a b : GNode G.tree) (hc : Comb.IsSubPairedTree G a b) (t : TTree)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some (X.plug ζ t))
    (hf : b.1 = addrExt a.1 X.lonePath) :
    (Comb.embeddedPairedTree hc).tree 0 = X.plug ζ .leaf := by
  let D := Comb.collapseDataOfDesc hc.1
  have hu : D.upper = X.plug ζ t := Option.some.inj (D.upper_eq.symm.trans ha)
  have hp : D.path = X.lonePath := by
    apply List.append_cancel_left (as := a.1.2)
    exact D.path_eq.trans (congrArg (fun z : Address w => z.2) hf)
  change Comb.collapseAt D.upper D.path = _
  rw [hu,hp,Comb.collapseAt]
  exact replaceAt_plug_lonePath X ζ t .leaf

end WaveTurbulence.Reg.Skeleton
