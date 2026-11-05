/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.FullTopCounts
public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily

/-! # LF states carry the actual transported fixed source vine family -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links

structure FamilyReconstruction (w : ℕ) (ι : Type*) where
  skeleton : Garden w
  family : CoreFamily skeleton ι
  plain : skeleton.IsPlain
  data : ReconstructionData skeleton
  layered : LayeredGarden w
  decodes : data.Decodes plain layered.garden

namespace FamilyReconstruction
variable {w : ℕ} {ι : Type*} (A : FamilyReconstruction w ι)

@[expose] noncomputable def familyState : FamilyState w ι := ⟨A.skeleton,A.family⟩

@[expose] def source {p : ℕ} {kind : Bool} (i : ι) (hc : CanonicalObject p kind A.layered)
    (helig : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (ht : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (hq : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))) :
    LFSource p kind A.layered where
  skeleton := A.skeleton
  plain := A.plain
  data := A.data
  decodes := A.decodes
  placement := A.family.placement i
  canonical := hc
  vineType := A.family.kind i
  support := A.family.atoms i
  upper := A.family.upper i
  core := A.family.core i
  selected := A.family.designated i
  eligible := helig
  treeCoherent := ht
  coupleCoherent := hq

@[expose] noncomputable def nextFamily (i : ι) (ε : Bool) :
    CoreFamily (chosenSkeleton A.skeleton (A.family.placement i) ε) ι := by
  cases ε
  · exact A.family
  · exact A.family.twist i

end FamilyReconstruction

/-- One admissible operation at a designated member of the current transported
original family. The construction retains all exceptional choices. -/
structure FamilyOperation {w p : ℕ} {kind : Bool} {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) where
  canonical : CanonicalObject p kind A.layered
  eligible : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
    (A.family.kind i) (A.family.atoms i) (A.family.upper i)
  treeCoherent : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode))
  coupleCoherent : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode))
  choice : Bool
  construction : LFConstruction (A.source i canonical eligible treeCoherent coupleCoherent) choice

namespace FamilyOperation
variable {w p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    (h : FamilyOperation (p := p) (kind := kind) A i)

@[expose] noncomputable def output : FamilyReconstruction w ι where
  skeleton := chosenSkeleton A.skeleton (A.family.placement i) h.choice
  family := A.nextFamily i h.choice
  plain := chosenSkeleton_plain _ _ A.plain h.choice
  data := h.construction.data
  layered := h.construction.output
  decodes := h.construction.decodes

/-- The original family is transported by the already proved actual M6 step. -/
theorem familyState_output : h.output.familyState =
    if h.choice then familyStep i A.familyState else A.familyState := by
  change (⟨chosenSkeleton A.skeleton (A.family.placement i) h.choice,A.nextFamily i h.choice⟩ : FamilyState w ι) = _
  cases h.choice <;> rfl

theorem output_canonical : CanonicalObject p kind h.output.layered := h.construction.canonical

theorem output_order : h.output.layered.garden.order = A.layered.garden.order := h.construction.order

theorem output_topOrder (j : Fin w) : h.output.layered.topOrder p j = A.layered.topOrder p j := h.construction.topOrder j

theorem output_isTrunc (Ntop Natt : ℕ) (hn : A.layered.garden.order ≤ Natt) :
    h.output.layered.IsTrunc p Ntop Natt ↔ A.layered.IsTrunc p Ntop Natt := h.construction.isTrunc Ntop Natt hn

end FamilyOperation
end WaveTurbulence.LFTwist
