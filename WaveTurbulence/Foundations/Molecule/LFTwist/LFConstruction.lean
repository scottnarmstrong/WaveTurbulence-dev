/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFReinsertData
public import WaveTurbulence.Foundations.Molecule.LFTwist.RawNativeCounts

/-! # Literal unit LF construction with freely chosen coherent exceptional objects

The intermediate and output forests/matchings are the actual reconstruction
data, not abstract normalized gardens. The two C4 insertion records express
unchanged outside nodes, partners, layers and signatures. The remaining layer
fields are precisely the fixed skeleton pre-layering and unchanged ordinary
native layerings from TARGET. Only combined *local* counts are constrained;
output canonicity and global top-tree count preservation are conclusions.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed

@[expose] noncomputable def coupleRoot {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (q : SourcePair S) (i : Fin 2) : Address w :=
  if i = 0 then inflatedPosition S D.tree (q.firstLeaf hS).toNode
  else inflatedPosition S D.tree (q.secondLeaf hS).toNode

structure LFConstruction {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}
    (s : LFSource p kind LG) (ε : Bool) where
  newTree : RegChain
  newCouple : RegCpl
  tree_wf : newTree.wf = true
  couple_wf : newCouple.wf = true
  midLayer : GNode ((s.midData ε newCouple couple_wf).forest (s.chosen_plain ε)) → ℕ
  mid_isLayering : IsLayering ((s.midData ε newCouple couple_wf).garden (s.chosen_plain ε)) midLayer
  outLayer : GNode ((s.finalData ε newTree newCouple tree_wf couple_wf).forest (s.chosen_plain ε)) → ℕ
  out_isLayering : IsLayering ((s.finalData ε newTree newCouple tree_wf couple_wf).garden (s.chosen_plain ε)) outLayer
  tail : TTree
  coupleInsertion : CoherentCoupleInsertion p (s.base ε)
    (layeredReconstruction (s.midData ε newCouple couple_wf) (s.chosen_plain ε) midLayer mid_isLayering)
    (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 0)
    (coupleRoot (s.baseData ε) (s.chosen_plain ε) (s.pairs ε s.exceptional) 1) newCouple
  treeInsertion : CoherentTreeInsertion p
    (layeredReconstruction (s.midData ε newCouple couple_wf) (s.chosen_plain ε) midLayer mid_isLayering)
    (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf) (s.chosen_plain ε) outLayer out_isLayering)
    (inflatedPosition (s.chosen ε) (s.midData ε newCouple couple_wf).tree (s.branches ε s.placement.lower).toNode)
    (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1) tail newTree
  coreLayers : ∀ b : GBranch s.skeleton.tree,
    layerAt LG (s.data.corePosition b) =
      layerAt (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf)
        (s.chosen_plain ε) outLayer out_isLayering)
        ((s.finalData ε newTree newCouple tree_wf couple_wf).corePosition (s.branches ε b))
  ordinaryTreeLayers : ∀ b : GBranch s.skeleton.tree, b ≠ s.placement.lower →
    ∀ q ∈ ((s.data.tree b).plug (nodeSign s.skeleton.sig b.1) .leaf).nodes,
    layerAt LG (addrExt (inflatedPosition s.skeleton s.data.tree b.toNode) q) =
      layerAt (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf)
        (s.chosen_plain ε) outLayer out_isLayering)
        (addrExt (inflatedPosition (s.chosen ε) (s.finalData ε newTree newCouple tree_wf couple_wf).tree
          (s.branches ε b).toNode) q)
  ordinaryCoupleLayers : ∀ q : SourcePair s.skeleton, q ≠ s.exceptional →
    ∀ (i : Fin 2) (r : Path), r ∈ ((decodedCouple (s.data.couple q)).tree i).nodes →
    layerAt LG (addrExt (coupleRoot s.data s.plain q i) r) =
      layerAt (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf)
        (s.chosen_plain ε) outLayer out_isLayering)
        (addrExt (coupleRoot (s.finalData ε newTree newCouple tree_wf couple_wf)
          (s.chosen_plain ε) (s.pairs ε q) i) r)
  combinedOrder : newTree.size + newCouple.size =
    (s.data.tree s.placement.lower).size + (s.data.couple s.exceptional).size
  combinedTopCount : rawTreeLayerCount LG s.data s.plain p s.placement.lower +
      rawCoupleLayerCount LG s.data s.plain p s.exceptional =
    rawTreeLayerCount (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf)
      (s.chosen_plain ε) outLayer out_isLayering)
      (s.finalData ε newTree newCouple tree_wf couple_wf) (s.chosen_plain ε) p (s.branches ε s.placement.lower) +
    rawCoupleLayerCount (layeredReconstruction (s.finalData ε newTree newCouple tree_wf couple_wf)
      (s.chosen_plain ε) outLayer out_isLayering)
      (s.finalData ε newTree newCouple tree_wf couple_wf) (s.chosen_plain ε) p (s.pairs ε s.exceptional)

namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

@[expose] noncomputable def data : ReconstructionData (s.chosen ε) :=
  s.finalData ε h.newTree h.newCouple h.tree_wf h.couple_wf

@[expose] noncomputable def output : LayeredGarden w :=
  layeredReconstruction h.data (s.chosen_plain ε) h.outLayer h.out_isLayering

/-- Both freely chosen exceptional reinsertions preserve the source canonical kind. -/
theorem canonical : CanonicalObject p kind h.output :=
  h.treeInsertion.canonical (h.coupleInsertion.canonical (s.base_canonical ε))

/-- Exact combined local order gives exact whole-garden order. -/
theorem order : h.output.garden.order = LG.garden.order :=
  s.finalData_order ε h.newTree h.newCouple h.tree_wf h.couple_wf h.combinedOrder

/-- The output carries actual updated reconstruction data for subsequent operations. -/
theorem decodes : h.data.Decodes (s.chosen_plain ε) h.output.garden := h.data.garden_decodes _

end LFConstruction
end WaveTurbulence.LFTwist
