/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalObject
public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeCollapseCanonical
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Replace

/-! # Literal C4 reinsertion data for the two LF exceptional objects

Outside agreement is the source's unchanged rest of the layered garden.
Signatures are retained explicitly: the C4 outside-agreement structures do not
contain that source requirement. No canonicity of the output is a field.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ}

/-- Insert a chosen regular tree into an actual nil-tree slot, keeping its
terminal subtree and the entire outside layered garden. -/
structure CoherentTreeInsertion (p : ℕ) (LG LH : LayeredGarden w)
    (a : Address w) (ζ : ℤˣ) (t : TTree) (X : RegChain) : Prop where
  wf : X.wf = true
  signature : LH.garden.sig = LG.garden.sig
  rootSign : nodeSign LG.garden.sig a = ζ
  oldEmbedding : ChainEmb LG.garden .nil ζ a t
  newEmbedding : ChainEmb LH.garden X ζ a t
  outside : OutAgreeT LG LH a (addrExt a RegChain.nil.lonePath) (addrExt a X.lonePath)
  pattern : TreePattern LH p X ζ a

/-- Insert a chosen regular couple at an actual positive/negative trivial
leaf pair, retaining every node, layer and matching outside its two roots. -/
structure CoherentCoupleInsertion (p : ℕ) (LG LH : LayeredGarden w)
    (a b : Address w) (Q : RegCpl) : Prop where
  wf : Q.wf = true
  signature : LH.garden.sig = LG.garden.sig
  positive : nodeSign LG.garden.sig a = 1
  negative : nodeSign LG.garden.sig b = -1
  oldEmbedding : Embeds LG.garden .triv a b
  newEmbedding : Embeds LH.garden Q a b
  outside : OutAgree LG LH a b
  pattern : LayerPattern LH p Q a b

/-- The actual tree reinsertion preserves the original source canonical kind. -/
theorem CoherentTreeInsertion.canonical {p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}
    {a : Address w} {ζ : ℤˣ} {t : TTree} {X : RegChain}
    (h : CoherentTreeInsertion p LG LH a ζ t X) (hc : CanonicalObject p kind LG) :
    CanonicalObject p kind LH := by
  have hnil : CohOn LG (RegChain.nil.linksAt ζ a) := by
    simp only [CohOn, RegChain.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  cases hc with
  | garden hc =>
    exact .garden (layerreg1_replace_tree_canonG hc rfl h.oldEmbedding hnil h.outside h.newEmbedding h.pattern)
  | couple hc =>
    exact .couple (layerreg1_replace_tree_canonC hc rfl h.oldEmbedding hnil h.outside h.signature h.newEmbedding h.pattern)

/-- The actual couple reinsertion preserves the original source canonical kind. -/
theorem CoherentCoupleInsertion.canonical {p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}
    {a b : Address w} {Q : RegCpl}
    (h : CoherentCoupleInsertion p LG LH a b Q) (hc : CanonicalObject p kind LG) :
    CanonicalObject p kind LH := by
  have hnil : CohOn LG (RegCpl.triv.linksAt a b) := by
    simp only [CohOn, RegCpl.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  cases hc with
  | garden hc =>
    exact .garden (layerreg1_replace_canonG hc rfl h.oldEmbedding hnil h.outside h.newEmbedding h.pattern)
  | couple hc =>
    exact .couple (layerreg1_replace_canonC hc rfl h.oldEmbedding hnil h.outside h.signature h.newEmbedding h.pattern)

end WaveTurbulence.LFTwist
