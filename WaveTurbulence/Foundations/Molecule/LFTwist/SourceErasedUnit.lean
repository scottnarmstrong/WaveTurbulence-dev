/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LayeredReconstructedUnit
public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalObject

/-! # Source-eligible erased units: canonical actual reconstructions and exact layers -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist RegRed
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- In all source core-vine cases, the erased skeleton twist has an actual
canonical layered reconstruction. Every physical node keeps its layer and
each original tree keeps its full layer-p count. This is the erased step,
before the freely chosen coherent exceptional objects are reinserted. -/
theorem source_erased_unit_exists {p : ℕ} {kind : Bool}
    (hc : CanonicalObject p kind (layeredReconstruction D hS layer hLayer))
    (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)
    {X : VineType} {B : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hcore : IsCoreCLVine S X B a P.lower) (hP : IsPlacementAt S B P.lower P)
    (helig : SourceLayerEligible (layeredReconstruction D hS layer hLayer) D hS
      (D.garden_decodes hS) P X B a) :
    ∃ LH : LayeredGarden w,
      (twistReconstruction S P hS D).Decodes (unitTwistGarden_plain S P hS) LH.garden ∧
      CanonicalObject p kind LH ∧ LH.garden.order = (D.garden hS).order ∧
      (∀ j, LH.topOrder p j = (layeredReconstruction D hS layer hLayer).topOrder p j) ∧
      ∀ n : GNode (D.forest hS), Links.layerAt LH (inflatedExchange S P D n.1) = layer n := by
  let LG := layeredReconstruction D hS layer hLayer
  let Q := expandedPlacement D hS (D.garden_decodes hS) P hq
  have he : SameLowerLayer LG Q := sourceExpanded_sameLowerLayer LG D hS (D.garden_decodes hS)
    P hq hc.criterion hcore hP helig
  let LH := erasedUnitLayered S P hS D layer hLayer hq he
  have hcan : CanonicalObject p kind LH := by
    cases hc with
    | garden hc =>
      exact .garden (sourceExpanded_unit_isCanonG LG D hS (D.garden_decodes hS) P hq hc hcore hP helig)
    | couple hc =>
      exact .couple (sourceExpanded_unit_isCanonC LG D hS (D.garden_decodes hS) P hq hc hcore hP helig)
  refine ⟨LH,erasedUnit_decodes S P hS D layer hLayer hnil hq he,hcan,
    unitLayerTwist_order LG Q he,?_,erasedUnit_layerAt S P hS D layer hLayer hnil hq he⟩
  intro j
  exact unitLayerTwist_topOrder LG Q he
    (sourceExpanded_same_tree LG D hS (D.garden_decodes hS) P hq hcore hP) p j

end WaveTurbulence.LFTwist
