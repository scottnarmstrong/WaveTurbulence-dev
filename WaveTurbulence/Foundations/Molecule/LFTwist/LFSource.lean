/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NormalizedChoice

/-! # Literal source data for one eligible LF operation

This permits the intermediate regular reconstructions in TARGET's sublayer
observation. In particular, it applies to the actual prime skeleton supplied
by propstructure2. Only the two designated attachments must be coherent.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links

structure LFSource {w : ℕ} (p : ℕ) (kind : Bool) (LG : LayeredGarden w) where
  skeleton : Garden w
  plain : skeleton.IsPlain
  data : ReconstructionData skeleton
  decodes : data.Decodes plain LG.garden
  placement : CorePlacement skeleton
  canonical : CanonicalObject p kind LG
  vineType : VineType
  support : Finset (GBranch skeleton.tree)
  upper : GBranch skeleton.tree
  core : IsCoreCLVine skeleton vineType support upper placement.lower
  selected : IsPlacementAt skeleton support placement.lower placement
  eligible : SourceLayerEligible LG data plain decodes placement vineType support upper
  treeCoherent : CohOn LG ((data.tree placement.lower).linksAt (nodeSign skeleton.sig placement.lower.1)
    (inflatedPosition skeleton data.tree placement.lower.toNode))
  coupleCoherent : CohOn LG ((data.couple (pairOfLeaf skeleton plain placement.retained)).linksAt
    (inflatedPosition skeleton data.tree ((pairOfLeaf skeleton plain placement.retained).firstLeaf plain).toNode)
    (inflatedPosition skeleton data.tree ((pairOfLeaf skeleton plain placement.retained).secondLeaf plain).toNode))

namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

@[expose] noncomputable def chosen (ε : Bool) : Garden w := chosenSkeleton s.skeleton s.placement ε

theorem chosen_plain (ε : Bool) : (s.chosen ε).IsPlain := chosenSkeleton_plain _ _ s.plain ε

@[expose] noncomputable def branches (ε : Bool) : GBranch s.skeleton.tree ≃ GBranch (s.chosen ε).tree :=
  chosenBranchEquiv s.skeleton s.placement ε

@[expose] noncomputable def pairs (ε : Bool) : SourcePair s.skeleton ≃ SourcePair (s.chosen ε) :=
  chosenPairEquiv s.skeleton s.placement s.plain ε

@[expose] noncomputable def exceptional : SourcePair s.skeleton :=
  pairOfLeaf s.skeleton s.plain s.placement.retained

@[expose] noncomputable def baseData (ε : Bool) : ReconstructionData (s.chosen ε) :=
  normalizedChoiceData s.data s.plain s.placement ε

@[expose] noncomputable def base (ε : Bool) : LayeredGarden w :=
  normalizedChoiceLayered LG s.data s.plain s.decodes s.placement s.canonical
    s.treeCoherent s.coupleCoherent s.core s.selected s.eligible ε

theorem base_decodes (ε : Bool) : (s.baseData ε).Decodes (s.chosen_plain ε) (s.base ε).garden :=
  normalizedChoice_decodes LG s.data s.plain s.decodes s.placement s.canonical
    s.treeCoherent s.coupleCoherent s.core s.selected s.eligible ε

theorem base_canonical (ε : Bool) : CanonicalObject p kind (s.base ε) :=
  normalizedChoice_canonical LG s.data s.plain s.decodes s.placement s.canonical
    s.treeCoherent s.coupleCoherent s.core s.selected s.eligible ε

end LFSource
end WaveTurbulence.LFTwist
