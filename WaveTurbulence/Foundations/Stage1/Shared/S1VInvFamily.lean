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

/-- A CL vine on the atom set of the twisted block has the same joints. -/
theorem vine_eq_site (c : CLVine G) (hc : c.atoms = Z.S0) : c.upper = Z.a0 ∧ c.lower = Z.P.lower := by
  obtain ⟨X, hX⟩ := c.isVine
  have hu : c.upper ∈ Z.S0 := hc ▸ c.upper_mem
  have hl : c.lower ∈ Z.S0 := hc ▸ c.lower_mem
  have d1 := (Mole.block_joint_degrees G.molecule hX.1).1
  have d2 := (Mole.block_joint_degrees G.molecule hX.1).2
  rw [hc] at d1 d2
  have j1 : c.upper = Z.a0 ∨ c.upper = Z.P.lower := by
    rcases block_degIn_cases Z.hB hu with ⟨h, _⟩ | ⟨_, h4⟩
    · exact h
    · omega
  have j2 : c.lower = Z.a0 ∨ c.lower = Z.P.lower := by
    rcases block_degIn_cases Z.hB hl with ⟨h, _⟩ | ⟨_, h4⟩
    · exact h
    · omega
  have hne : c.upper ≠ c.lower := hX.1.2.2.2.1
  have hnotl : c.upper ≠ Z.P.lower := by
    intro h
    apply c.notParentUpper
    rw [hc, h]
    exact Z.ip_old_lower.mpr Z.pO_mem
  have hup : c.upper = Z.a0 := j1.resolve_right hnotl
  refine ⟨hup, ?_⟩
  rcases j2 with h | h
  · exact absurd (hup.trans h.symm) hne
  · exact h

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

/-- `IsVFamily` for a pair (garden, family). -/
@[expose] def IsVFam {G : Garden w} (F : CoreFamily G ι) : Prop :=
  (∀ i, ∃ c ∈ vinesV G, c.atoms = F.atoms i ∧ c.upper = F.upper i ∧ c.lower = (F.placement i).lower) ∧
  (∀ c ∈ vinesV G, (∃ X, IsCoreCLVine G X c.atoms c.upper c.lower) →
    ∃ i, c.atoms = F.atoms i ∧ c.upper = F.upper i ∧ c.lower = (F.placement i).lower)

theorem isVFamily_iff (A : FamilyReconstruction w ι) : IsVFamily A ↔ IsVFam A.family := Iff.rfl

theorem member_group {G : Garden w} {F : CoreFamily G ι} (hF : IsVFam F) (i : ι) :
    ∃ S ∈ maximalGroups G.molecule, IsIngredient G.molecule S (F.atoms i) := by
  obtain ⟨c, ⟨S, hS, hing, _⟩, hat, -, -⟩ := hF.1 i
  exact ⟨S, hS, hat ▸ hing⟩

/-- The twist site of a member of a `𝒱`-family. -/
@[expose] noncomputable def siteOfMember {G : Garden w} {F : CoreFamily G ι} (hF : IsVFam F) (i : ι) :
    TwistGroupSite G where
  P := F.placement i
  S0 := F.atoms i
  a0 := F.upper i
  hB := (F.core i).1.1
  hCL := (F.core i).2.1
  hP := F.designated i
  Sg := (member_group hF i).choose
  hSg := (member_group hF i).choose_spec.1
  hS0 := (member_group hF i).choose_spec.2

/-- **A unit twist at a member preserves the `𝒱`-family property** (choice true). -/
theorem isVFam_twist {G : Garden w} {F : CoreFamily G ι} (hF : IsVFam F) (i : ι) :
    IsVFam (F.twist i) := by
  let Z := siteOfMember hF i
  constructor
  · intro j
    obtain ⟨c, hc, hat, hup, hlow⟩ := hF.1 j
    obtain ⟨c', hc', ha', hu', hl'⟩ := Z.vinesV_image hc
    refine ⟨c', hc', ?_, ?_, ?_⟩
    · rw [ha', hat]; rfl
    · rw [hu', hup]; rfl
    · rw [hl', hlow]; exact (F.nextPlacement_lower i j).symm
  · intro c' hc' ⟨X, hX⟩
    obtain ⟨c, hc, hat, hup, hlow⟩ := Z.vinesV_preimage hc'
    by_cases hS0 : c.atoms = F.atoms i
    · obtain ⟨hu, hl⟩ := Z.vine_eq_site c hS0
      refine ⟨i, ?_, ?_, ?_⟩
      · rw [← hat, hS0]; rfl
      · rw [← hup]; exact congrArg _ hu
      · rw [← hlow]; rw [show c.lower = (F.placement i).lower from hl]
        exact (F.nextPlacement_lower i i).symm
    · obtain ⟨S, hS, hing, hcond⟩ := hc
      have hsep := Z.sep_of_ing hS hing hS0
      have hcore : IsCoreCLVine G X c.atoms c.upper c.lower :=
        Z.core_pull hsep (by rw [hat, hup, hlow]; exact hX)
      obtain ⟨j, hj1, hj2, hj3⟩ := hF.2 c ⟨S, hS, hing, hcond⟩ ⟨X, hcore⟩
      refine ⟨j, ?_, ?_, ?_⟩
      · rw [← hat, hj1]; rfl
      · rw [← hup, hj2]; rfl
      · rw [← hlow, hj3]; exact (F.nextPlacement_lower i j).symm

/-- **Part (a)**: one LF operation preserves `IsVFamily`. -/
theorem isVFamily_output {p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι} {i : ι}
    (hA : IsVFamily A) (op : FamilyOperation (p := p) (kind := kind) A i) : IsVFamily op.output := by
  have key : ∀ ε : Bool, IsVFam (A.nextFamily i ε) := by
    intro ε
    cases ε
    · exact hA
    · exact isVFam_twist hA i
  exact key op.choice

/-- **Part (a)**: a batch of LF operations preserves `IsVFamily`. -/
theorem isVFamily_batch {p : ℕ} {kind : Bool} {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hA : IsVFamily A) : IsVFamily B := by
  induction h with
  | nil => exact hA
  | skip i h ih => exact ih hA
  | apply op h ih => exact ih (isVFamily_output hA op)

end Family

end WaveTurbulence.Stage1
