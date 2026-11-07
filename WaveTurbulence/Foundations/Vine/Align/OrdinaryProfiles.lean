/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.Outputs
public import WaveTurbulence.Foundations.VineEst.LeafOp2
/-! Pair-type profiles on the actual ordinary native-leaf correspondence.
These are ingredients for R-SLOT, not an assertion of slot-kernel invariance. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine Links

/-- Read the actual layered profile at a leaf of its decoded reconstruction. -/
theorem typeProfiles_dataLeaf {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (LG : LayeredGarden w) (hspec : layeredReconstruction D hS layer hLayer = LG)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (x : GLeaf (D.forest hS)) :
    typeProfiles LG f x.1 = f (layerAt LG x.1) x.1.1 ((D.garden hS).pair x).1.1 := by
  subst LG
  exact (typeProfiles_leaf (layeredReconstruction D hS layer hLayer) f x).trans
    (congrArg (fun n => f n x.1.1 ((D.garden hS).pair x).1.1)
      (layerAt_node (layeredReconstruction D hS layer hLayer) x.toNode).symm)

/-- Ordinary native leaves carry the same actual pair-type profile through an LF construction. -/
theorem ordinary_typeProfiles {w p d : ℕ} {kind ε : Bool} {LG : LayeredGarden w}
    {s : LFSource p kind LG} (h : LFConstruction s ε)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain ε)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain ε)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer' = h.output)
    {x : GLeaf (s.data.forest s.plain)} {y : GLeaf (h.data.forest (s.chosen_plain ε))}
    (hc : h.OrdCorr x y) (f : ℕ → Fin w → Fin w → Mom d → ℝ) :
    typeProfiles LG f x.1 = typeProfiles h.output f y.1 := by
  rw [typeProfiles_dataLeaf s.data s.plain layer hLayer LG hspec,
    typeProfiles_dataLeaf h.data (s.chosen_plain ε) layer' hLayer' h.output hspec']
  obtain ⟨x', y', hp, hx, hy⟩ := hc.pair
  rw [hc.layer, hc.index, hx, hy, hp.index]

/-- The same profile equality on the public actual-family-operation leaf carrier. -/
theorem operation_typeProfiles {w p d : ℕ} {kind : Bool} {ι : Type*}
    {A : FamilyReconstruction w ι} {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    {x : GLeaf A.layered.garden.tree} {y : GLeaf op.output.layered.garden.tree}
    (hc : op.LeafCorr x y) (f : ℕ → Fin w → Fin w → Mom d → ℝ) :
    typeProfiles A.layered f x.1 = typeProfiles op.output.layered f y.1 := by
  rw [typeProfiles_leaf, typeProfiles_leaf]
  obtain ⟨x', y', hp, hx, hy⟩ := hc.pair
  rw [hc.layer, hc.index, hx, hy, hp.index]

end WaveTurbulence.VineAlign
