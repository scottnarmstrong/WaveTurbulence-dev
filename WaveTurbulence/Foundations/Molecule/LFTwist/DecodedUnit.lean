/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructedUnitGarden

/-! # Erased-unit reconstruction in any literal decoded ambient garden -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist

/-- The naturality theorem is independent of the chosen proof/carrier presentation
of the actual decoded ambient garden. -/
theorem decoded_unit_decodes {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (P : CorePlacement S)
    (hnil : D.tree P.lower = .nil) (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (twistReconstruction S P hS D).Decodes (unitTwistGarden_plain S P hS)
      (unitTwistGarden G (expandedPlacement D hS hd P hq)) := by
  have hg : G = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst G
  exact Eq.mp (congrArg ((twistReconstruction S P hS D).Decodes (unitTwistGarden_plain S P hS))
    (reconstructed_unit_garden S P hS D hnil hq))
    ((twistReconstruction S P hS D).garden_decodes (unitTwistGarden_plain S P hS))

end WaveTurbulence.LFTwist
