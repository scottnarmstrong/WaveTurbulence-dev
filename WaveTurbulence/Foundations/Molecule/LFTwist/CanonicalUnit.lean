/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalCriterion
public import WaveTurbulence.Foundations.Molecule.LFTwist.RootClosure

/-! # Uniform canonicity of the actual collapsed LF unit twist

TARGET lftwistprop L1485–L1487, including every core vine case. The
threshold-cut correspondence preserves both node and parent layers and
transports the literal completely paired subtree condition.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w) (P : CorePlacement LG.garden)

/-- For designated source CL sites, the actual collapsed unit twist
preserves the canonical garden class in both directions. -/
theorem unitLayerTwist_isCanonG (he : SameLowerLayer LG P)
    (hsame : P.lower.1.1 = (LG.garden.pair P.retained).1.1) (p : ℕ) :
    IsCanonG (p+1) (unitLayerTwist LG P he) ↔ IsCanonG (p+1) LG := by
  change (4 ≤ w ∧ (unitTwistGarden LG.garden P).IsPlain ∧
    (unitTwistGarden LG.garden P).Irreducible ∧ (unitLayerTwist LG P he).CanonCriterion p) ↔ _
  have hp : (unitTwistGarden LG.garden P).IsPlain ↔ LG.garden.IsPlain := by
    constructor
    · intro h
      have ht := unitTwistGarden_plain (unitTwistGarden LG.garden P) (reversePlacement LG.garden P) h
      exact (unitTwistGarden_involutive LG.garden P) ▸ ht
    · exact unitTwistGarden_plain LG.garden P
  exact and_congr_right (fun _ => and_congr hp
    (and_congr (unitTwist_irreducible P hsame) (unitLayerTwist_canonCriterion LG P he p)))

/-- The canonical couple class is also preserved, including the source signature convention. -/
theorem unitLayerTwist_isCanonC {LG : LayeredGarden 2} (P : CorePlacement LG.garden)
    (he : SameLowerLayer LG P) (p : ℕ) :
    IsCanonC (p+1) (unitLayerTwist LG P he) ↔ IsCanonC (p+1) LG := by
  have hcpl : IsCouple (unitTwistGarden LG.garden P) ↔ IsCouple LG.garden := by
    constructor
    · intro h
      have ht := unitTwistGarden_couple (reversePlacement LG.garden P) h
      exact (unitTwistGarden_involutive LG.garden P) ▸ ht
    · exact unitTwistGarden_couple P
  exact and_congr hcpl (unitLayerTwist_canonCriterion LG P he p)

end WaveTurbulence.LFTwist
