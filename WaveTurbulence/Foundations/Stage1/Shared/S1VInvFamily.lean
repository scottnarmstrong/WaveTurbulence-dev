/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.Stage1.Shared.S1Cong
public import WaveTurbulence.Foundations.Molecule.UnitTwistInvolution
public import WaveTurbulence.Foundations.Molecule.TwistFamilyExtensionality
public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements
import Mathlib.Tactic

/-!
# Part (a) of `GAP.congEquiv`: `IsVFamily` is preserved by LF operations and batches

A choice-false operation leaves skeleton and family unchanged.  A choice-true operation unit-twists the
skeleton at a member of the family, which is an ingredient of a maximal group (`IsVFamily`); then
`vinesV_image`/`vinesV_preimage` transport `𝒱`, and the M6 pair data transports the core property
(backwards through the cast `unitTwistGarden_involutive`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- A core CL vine can be pulled back across a garden equality that is the identity on addresses. -/
theorem isCoreCLVine_cast {K G : Garden w} (hKG : K = G) (e : GBranch G.tree ≃ GBranch K.tree)
    (he : ∀ b, (e b).1 = b.1) {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsCoreCLVine K X (S.image e) (e a) (e b)) : IsCoreCLVine G X S a b := by
  subst hKG
  have : e = Equiv.refl _ := Equiv.ext fun b => Subtype.ext (he b)
  subst this
  simpa using h

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite G)

/-- **Backward core transfer**: a core CL vine of the twisted garden separated from the twisted block
is a core CL vine of the original garden (via the M6 pair data at the reverse placement). -/
theorem core_pull {c : CLVine G} (hsep : SeparatedGroups Z.S0 c.atoms) {X : VineType}
    (hcore : IsCoreCLVine Z.target X (twistedAtoms G Z.P c.atoms) (coreBranchEquiv G Z.P c.upper)
      (coreBranchEquiv G Z.P c.lower)) : IsCoreCLVine G X c.atoms c.upper c.lower := by
  obtain ⟨Q, hQ⟩ := corePlacement_at_vine Z.target hcore
  have hR := reversePlacement_at_twistedAtoms G Z.P Z.hB Z.hCL Z.hP
  let D : CorePairData Z.target (reversePlacement G Z.P) Q :=
    { left := twistedAtoms G Z.P Z.S0
      right := twistedAtoms G Z.P c.atoms
      upperLeft := coreBranchEquiv G Z.P Z.a0
      upperRight := coreBranchEquiv G Z.P c.upper
      blockLeft := Z.iso.isBlock_img Z.hB
      clLeft := clParentPattern_twistedAtoms G Z.P Z.hB Z.hCL Z.hP
      atLeft := hR
      blockRight := by rw [hQ.1]; exact hcore.1.1
      clRight := by rw [hQ.1]; exact hcore.2.1
      atRight := ⟨rfl, fun i => by rw [hQ.1]; exact hQ.2 i⟩
      separated := separatedGroups_twisted hsep }
  have hcore' : IsCoreCLVine Z.target X D.right D.upperRight Q.lower := by
    rw [hQ.1]; exact hcore
  have h2 := D.core_preserved hcore'
  rw [hQ.1] at h2
  have himg : twistedAtoms Z.target (reversePlacement G Z.P) (twistedAtoms G Z.P c.atoms) =
      c.atoms.image ((coreBranchEquiv G Z.P).trans
        (coreBranchEquiv Z.target (reversePlacement G Z.P))) := by
    unfold twistedAtoms isoAtoms
    rw [Finset.image_image]; rfl
  have h3 := h2
  change IsCoreCLVine (unitTwistGarden Z.target (reversePlacement G Z.P)) X
    (twistedAtoms Z.target (reversePlacement G Z.P) (twistedAtoms G Z.P c.atoms)) _ _ at h3
  rw [himg] at h3
  exact isCoreCLVine_cast (unitTwistGarden_involutive G Z.P)
    ((coreBranchEquiv G Z.P).trans (coreBranchEquiv Z.target (reversePlacement G Z.P)))
    (fun b => coreBranchEquiv_twice_val G Z.P b) h3

end TwistGroupSite
section Family
variable {ι : Type*}

end Family

end WaveTurbulence.Stage1
