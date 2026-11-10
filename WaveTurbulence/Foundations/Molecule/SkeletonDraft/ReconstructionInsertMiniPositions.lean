/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionNodeLocation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionInsertMini
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PositionTransportFromLocalHoles

/-! # Actual-node B insertion transports every original attachment and core address -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.insertMini_local_hole {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (m : MiniTreeCode) (b : GBranch S.tree) :
    addrExt (pinnedRelocate target.1 m (inflatedPosition S D.tree b.toNode))
      ((D.insertMini hS target.1 m).tree b).lonePath =
        relocate target.1 m.c m.lone (D.corePosition b) := by
  exact insertedChain_hole_of_location (D.tree b) S.sig (nodeSign S.sig b.1)
    (inflatedPosition S D.tree b.toNode) target.1 m (inflatedPosition_sign S D.tree b.toNode)
    (D.node_chain_location hS target b)

theorem ReconstructionData.insertMini_position {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (target : GNode (D.forest hS))
    (m : MiniTreeCode) (a : GNode S.tree) :
    inflatedPosition S (D.insertMini hS target.1 m).tree a =
      pinnedRelocate target.1 m (inflatedPosition S D.tree a) :=
  inflatedPosition_transport_of_local_holes D (D.insertMini hS target.1 m) target.1 m
    (D.insertMini_local_hole hS target m) a

end WaveTurbulence.Reg.Skeleton
