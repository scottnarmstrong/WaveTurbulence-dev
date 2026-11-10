/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.BranchLayering
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.AttachmentMomenta
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # The actual induced skeleton pre-layering

TARGET L1461–L1463: the layer of an original branching node is the layer
of the lone leaf of its attached regular tree. This supplies only branch
layers, as the source says, and derives their monotonicity.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton RegRed

/-- The inherited layer is exactly the source retained core-node layer. -/
@[expose] noncomputable def inducedPrelayer {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) : GBranch S.tree → ℕ :=
  coreLayer LG D hS hd

/-- The retained old child lies below its old parent after inserting every actual regular tree. -/
theorem decodedCoreBranch_child_desc {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (b c : GBranch S.tree) (i : Fin 3)
    (hc : c.toNode = b.child i) :
    (D.decodedCoreBranch hS hd b).toNode.IsDesc (D.decodedCoreBranch hS hd c).toNode := by
  have hi : inflatedPosition S D.tree c.toNode = addrExt (D.corePosition b) [i] :=
    (congrArg (inflatedPosition S D.tree) hc).trans (D.core_child_position b i)
  have hp : D.corePosition c = addrExt (D.corePosition b) ([i] ++ (D.tree c).lonePath) := by
    unfold ReconstructionData.corePosition
    rw [hi]
    exact addrExt_append _ _ _
  change (D.corePosition b).1 = (D.corePosition c).1 ∧ (D.corePosition b).2 <+: (D.corePosition c).2
  rw [hp]
  exact ⟨rfl,⟨[i] ++ (D.tree c).lonePath,rfl⟩⟩

/-- TARGET L1463: any full layering induces a genuine branch pre-layering of its skeleton. -/
theorem inducedPrelayer_isBranchPrelayering {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) :
    IsBranchPrelayering S (inducedPrelayer LG D hS hd) := by
  intro b c i hc
  exact LG.layer_le_of_isDesc (decodedCoreBranch_child_desc D hS hd b c i hc)

end WaveTurbulence.LFTwist
