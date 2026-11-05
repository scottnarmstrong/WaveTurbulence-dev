/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestBranches
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Literal layer inheritance on actual completely paired rooted subforests -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg.Skeleton

theorem rootedSubforest_ext {w v : ℕ} {tree : Fin w → TTree}
    (E F : Comb.RootedSubforest tree v) (h : ∀ j, E.root j = F.root j) : E = F := by
  cases E with
  | mk er es eh ei =>
    cases F with
    | mk fr fs fh fi =>
      have hr : er = fr := funext h
      subst fr
      have hs : es = fs := funext (fun j => Option.some.inj ((eh j).symm.trans (fh j)))
      subst fs
      rfl

theorem inducedGarden_congr {w v : ℕ} {G : Garden w}
    (E F : Comb.RootedSubforest G.tree v) (h : E = F)
    (he : G.CompletelyPaired E.leafSet) (hf : G.CompletelyPaired F.leafSet) :
    E.inducedGarden he = F.inducedGarden hf := by
  cases h
  rfl

theorem subforest_node_leaf {w v : ℕ} {tree : Fin w → TTree}
    (E : Comb.RootedSubforest tree v) (ℓ : GLeaf E.shape) :
    E.nodeEmbedding ℓ.toNode = (E.leafEmbedding ℓ).toNode := Subtype.ext rfl

theorem rootedSubforest_isLayering {w v : ℕ} (LG : LayeredGarden w)
    (E : Comb.RootedSubforest LG.garden.tree v)
    (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    IsLayering (Comb.RootedSubforest.inducedGarden E hc) (fun a => LG.layer (E.nodeEmbedding a)) := by
  constructor
  · intro b i
    change LG.layer (E.nodeEmbedding (b.child i)) ≤ LG.layer (E.nodeEmbedding b.toNode)
    let b' : GBranch E.shape := b
    exact (congrArg LG.layer (subforest_node_child E b' i)).trans_le
      (LG.isLayering.1 (subforestBranchEmbedding E b') i)
  · intro ℓ
    change LG.layer (E.nodeEmbedding ℓ.toNode) =
      LG.layer (E.nodeEmbedding ((Comb.RootedSubforest.inducedGarden E hc).pair ℓ).toNode)
    let ℓ' : GLeaf E.shape := ℓ
    have h := congrArg (fun q : GLeaf LG.garden.tree => LG.layer q.toNode)
      (Comb.RootedSubforest.inducedGarden_pair E hc ℓ')
    exact (congrArg LG.layer (subforest_node_leaf E ℓ')).trans
      ((LG.isLayering.2 (E.leafEmbedding ℓ')).trans
        (h.symm.trans (congrArg LG.layer
          (subforest_node_leaf E ((Comb.RootedSubforest.inducedGarden E hc).pair ℓ'))).symm))

/-- Both the actual induced pairing and all inherited layers are retained. -/
noncomputable def rootedLayeredGarden {w v : ℕ} (LG : LayeredGarden w)
    (E : Comb.RootedSubforest LG.garden.tree v)
    (hc : LG.garden.CompletelyPaired (Comb.RootedSubforest.leafSet E)) : LayeredGarden v where
  garden := Comb.RootedSubforest.inducedGarden E hc
  layer := fun a => LG.layer (E.nodeEmbedding a)
  isLayering := rootedSubforest_isLayering LG E hc

end WaveTurbulence.RegRed
