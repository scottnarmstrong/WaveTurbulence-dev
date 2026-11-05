/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.Prelayering
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden

/-! # Put any literal decoded layered object on its reconstruction carrier -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton RegRed
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (LG : LayeredGarden w) (hd : D.Decodes hS LG.garden)

include hd in
theorem decoded_forest : D.forest hS = LG.garden.tree := congrArg Raw.tree hd.2

@[expose] noncomputable def decodedLayer : GNode (D.forest hS) → ℕ :=
  fun n => LG.layer ⟨n.1,by rw [← decoded_forest D hS LG hd]; exact n.2⟩

theorem decodedLayer_isLayering : IsLayering (D.garden hS) (decodedLayer D hS LG hd) := by
  rcases LG with ⟨G,layer,hLayer⟩
  have he : G = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst G
  exact hLayer

theorem decodedLayered_eq :
    layeredReconstruction D hS (decodedLayer D hS LG hd) (decodedLayer_isLayering D hS LG hd) = LG := by
  rcases LG with ⟨G,layer,hLayer⟩
  have he : G = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst G
  rfl

end WaveTurbulence.LFTwist
