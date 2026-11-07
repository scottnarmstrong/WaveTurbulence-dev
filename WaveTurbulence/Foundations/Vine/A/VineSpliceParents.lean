/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceQuotient
/-! The old-name quotient identification preserves parent relations and every
inherited pre-layer. This is additional structure beyond a bare molecule iso. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice
variable {w : ℕ} {G H K : Garden w} {cls : GBranch G.tree → Option (GBranch G.tree)}

/-- The quotient branch identification preserves actual branching-node parents. -/
theorem spliceBranchEquiv_parent (M : SpMap G H cls) (N : SpMap G K cls)
    (v : GBranch H.tree) (hv : v.1.2 ≠ []) :
    let e := spliceBranchEquiv M N
    let hn : (e v).1.2 ≠ [] := fun h => hv ((spliceBranchEquiv_root M N v).mp h)
    e (GNode.parent v.toNode hv) = GNode.parent (e v).toNode hn := by
  dsimp only
  let e := spliceBranchEquiv M N
  have hn : (e v).1.2 ≠ [] := fun h => hv ((spliceBranchEquiv_root M N v).mp h)
  have ho : (M.ob v).1.2 ≠ [] := fun h => hv ((M.ob_root v).mp h)
  have hon : (N.ob (e v)).1.2 ≠ [] := fun h => hn ((N.ob_root (e v)).mp h)
  have hp : GNode.parent (N.ob (e v)).toNode hon = GNode.parent (M.ob v).toNode ho := by
    apply Subtype.ext
    exact congrArg (fun b : GBranch G.tree => (b.1.1, b.1.2.dropLast)) (spliceBranchEquiv_comm M N v)
  apply N.ob_inj
  rw [spliceBranchEquiv_comm, M.ob_parent v hv ho, N.ob_parent (e v) hn hon]
  exact congrArg (repC cls) hp.symm

/-- Every pre-layer pulled back from the original branch names is unchanged. -/
theorem spliceBranchEquiv_layer (M : SpMap G H cls) (N : SpMap G K cls)
    (layer : GBranch G.tree → ℕ) (v : GBranch H.tree) :
    layer (N.ob (spliceBranchEquiv M N v)) = layer (M.ob v) :=
  congrArg layer (spliceBranchEquiv_comm M N v)

end WaveTurbulence.VineA
