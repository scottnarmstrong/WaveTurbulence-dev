/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBranchRealization
import Mathlib.Tactic

/-! # Parent inheritance and joint separation in pruned regions
TARGET `block_clcn`: the second CN joint is outside the first joint's
pruned descendant region, including when both joints lie in one tree.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem pruned_node_nonroot {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {v : GNode G.tree} (hv : InCLPrunedRegion G S a b v) (hne : v ≠ a.toNode) : v.1.2 ≠ [] := by
  intro hn
  have ha : a.1.2 = [] := List.prefix_nil.mp (hn ▸ hv.1.2)
  exact hne (Subtype.ext (Prod.ext hv.1.1.symm (hn.trans ha.symm)))

theorem pruned_parent {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {v : GNode G.tree} (hv : InCLPrunedRegion G S a b v) (hne : v ≠ a.toNode)
    (hn : v.1.2 ≠ []) :
    InCLPrunedRegion G S a b (GNode.parent v hn).toNode := by
  refine ⟨⟨hv.1.1,proper_prefix_dropLast hv.1.2 ?_⟩,?_⟩
  · intro hp
    exact hne (Subtype.ext (Prod.ext hv.1.1.symm hp.symm))
  · intro j hj i hi hd
    exact hv.2 j hj i hi ⟨hd.1,hd.2.trans (List.dropLast_prefix _)⟩

end WaveTurbulence.Mole
