/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
/-! VINE-A2: the trace's atom bijection transports the indexed core family.
These identities tie molecular sigma transport to the actual LF family data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.LFTwist

/-- Composition of the literal atom-set maps. -/
theorem molIsoTrans_img {w : ℕ} {G H K : Garden w} (F : MolIso G.molecule H.molecule)
    (J : MolIso H.molecule K.molecule) (S : Finset (GBranch G.tree)) :
    (molIsoTrans F J).img S = J.img (F.img S) := by
  change S.image (J.e ∘ F.e) = (S.image F.e).image J.e
  rw [Finset.image_image]

namespace BatchIso
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

end BatchIso
end WaveTurbulence.VineA
