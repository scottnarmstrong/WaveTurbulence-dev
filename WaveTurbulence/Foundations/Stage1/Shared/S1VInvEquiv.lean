/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvMap
import Mathlib.Tactic

/-!
# `𝒱` is equivariant along the unit twist (TARGET `defcong`, L1934-L1937)

For a unit twist at a vine of a maximal group, `vinesV` of the twisted skeleton is the image of `vinesV`
of the original skeleton along `unitTwistDirectedIso` (vines are matched by atoms, upper and lower joint).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite G)

/-- The membership condition of `vinesV` for a fixed group. -/
@[expose] def Cond {G : Garden w} (S : Finset (GBranch G.tree)) (c : CLVine G) : Prop :=
  (∃ a b, IsVC G.molecule S a b ∧ ¬ IsRootVC G S) ∨
    ((∃ a b, IsHVC G.molecule S a b) ∨ IsRootVC G S) ∧
      ((∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T) ∨ ¬ IsTopIngredient S c)

theorem cond_iff {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (c : CLVine G)
    (hc : Z.Good c.atoms) (hing : IsIngredient G.molecule S c.atoms) :
    Cond S c ↔ Cond (twistedAtoms G Z.P S) (Z.mapVine c hc) := by
  have hSg := Z.group_good hS
  have hvc : (∃ a b, IsVC G.molecule S a b) ↔
      ∃ a b, IsVC Z.target.molecule (twistedAtoms G Z.P S) a b := by
    constructor
    · rintro ⟨a, b, h⟩; exact ⟨_, _, Z.iso.isVC_img h⟩
    · rintro ⟨a', b', h⟩
      obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
      obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
      exact ⟨a, b, Z.iso.isVC_img_iff.mp h⟩
  have hhvc : (∃ a b, IsHVC G.molecule S a b) ↔
      ∃ a b, IsHVC Z.target.molecule (twistedAtoms G Z.P S) a b := by
    constructor
    · rintro ⟨a, b, h⟩; exact ⟨_, _, Z.iso.isHVC_img h⟩
    · rintro ⟨a', b', h⟩
      obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
      obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
      exact ⟨a, b, Z.iso.isHVC_img_iff.mp h⟩
  have hcn : (∃ T, IsIngredient G.molecule S T ∧ IsCNVine G T) ↔
      ∃ T', IsIngredient Z.target.molecule (twistedAtoms G Z.P S) T' ∧ IsCNVine Z.target T' := by
    constructor
    · rintro ⟨T, hT, hcn⟩
      exact ⟨twistedAtoms G Z.P T, Z.iso.isIngredient_img hT, (Z.cn_iff (Z.ing_good hS hT)).mpr hcn⟩
    · rintro ⟨T', hT', hcn'⟩
      have hT : IsIngredient G.molecule S (Z.iso.symm.img T') := by
        have h : IsIngredient Z.target.molecule (Z.iso.img S) (Z.iso.img (Z.iso.symm.img T')) := by
          rw [Z.iso.img_symm_img]; exact hT'
        exact Z.iso.isIngredient_img_iff.mp h
      refine ⟨_, hT, (Z.cn_iff (Z.ing_good hS hT)).mp ?_⟩
      have e1 : twistedAtoms G Z.P (Z.iso.symm.img T') = T' := Z.iso.img_symm_img _
      rw [e1]; exact hcn'
  have htop : IsTopIngredient S c ↔
      IsTopIngredient (twistedAtoms G Z.P S) (Z.mapVine c hc) :=
    ⟨Z.top_fwd hS c hc hing, Z.top_bwd hS c hc hing⟩
  have hroot := Z.root_iff hSg
  unfold Cond
  simp only [exists_and_right, hvc, hhvc, hcn, htop, hroot]

/-- Membership in `𝒱` is transported (forward). -/
theorem mapVine_mem {c : CLVine G} (hc : c ∈ vinesV G) :
    ∃ hg : Z.Good c.atoms, Z.mapVine c hg ∈ vinesV Z.target := by
  obtain ⟨S, hS, hing, hcond⟩ := hc
  have hg := Z.ing_good hS hing
  refine ⟨hg, twistedAtoms G Z.P S, Z.iso.maximalGroups_img hS, Z.iso.isIngredient_img hing, ?_⟩
  exact (Z.cond_iff hS c hg hing).mp hcond

/-- **Equivariance of `𝒱` (image)**: every vine of `𝒱` is carried to a vine of `𝒱` of the twisted
skeleton, with image atoms and joints. -/
theorem vinesV_image {c : CLVine G} (hc : c ∈ vinesV G) :
    ∃ c' ∈ vinesV Z.target, c'.atoms = twistedAtoms G Z.P c.atoms ∧
      c'.upper = coreBranchEquiv G Z.P c.upper ∧ c'.lower = coreBranchEquiv G Z.P c.lower := by
  obtain ⟨hg, hm⟩ := Z.mapVine_mem hc
  exact ⟨_, hm, rfl, rfl, rfl⟩

/-- **Equivariance of `𝒱` (preimage)**: every vine of `𝒱` of the twisted skeleton comes from a vine
of `𝒱` of the original skeleton. -/
theorem vinesV_preimage {c' : CLVine Z.target} (hc : c' ∈ vinesV Z.target) :
    ∃ c ∈ vinesV G, twistedAtoms G Z.P c.atoms = c'.atoms ∧
      coreBranchEquiv G Z.P c.upper = c'.upper ∧ coreBranchEquiv G Z.P c.lower = c'.lower := by
  obtain ⟨S', hS', hing', hcond'⟩ := hc
  have hS : Z.iso.symm.img S' ∈ maximalGroups G.molecule := by
    have h : Z.iso.img (Z.iso.symm.img S') ∈ maximalGroups Z.target.molecule := by
      rw [Z.iso.img_symm_img]; exact hS'
    exact Z.iso.maximalGroups_img_iff.mp h
  have hing : IsIngredient G.molecule (Z.iso.symm.img S') (Z.iso.symm.img c'.atoms) := by
    have h : IsIngredient Z.target.molecule (Z.iso.img (Z.iso.symm.img S'))
        (Z.iso.img (Z.iso.symm.img c'.atoms)) := by
      rw [Z.iso.img_symm_img, Z.iso.img_symm_img]; exact hing'
    exact Z.iso.isIngredient_img_iff.mp h
  have hg := Z.ing_good hS hing
  set c := Z.pullVine c' hg with hcdef
  have hmc : Z.mapVine c hg = c' := by
    apply CLVine.ext'
    · exact Z.iso.img_symm_img _
    · exact Z.iso.e.apply_symm_apply _
    · exact Z.iso.e.apply_symm_apply _
  have hcond := (Z.cond_iff hS c hg hing).mpr (by
    have e1 : twistedAtoms G Z.P (Z.iso.symm.img S') = S' := Z.iso.img_symm_img _
    rw [e1, hmc]; exact hcond')
  refine ⟨c, ⟨_, hS, hing, hcond⟩, ?_, ?_, ?_⟩
  · exact Z.iso.img_symm_img _
  · exact Z.iso.e.apply_symm_apply _
  · exact Z.iso.e.apply_symm_apply _

/-- **`vinesV` is equivariant along `unitTwistDirectedIso`**: as sets of (atoms, upper joint, lower
joint), `vinesV` of the twisted skeleton is the image of `vinesV` of the skeleton under the branch
bijection `coreBranchEquiv` (`= (unitTwistDirectedIso G P).branches`). -/
theorem vinesV_equivariant :
    {t | ∃ c' ∈ vinesV Z.target, t = (c'.atoms, c'.upper, c'.lower)} =
      {t | ∃ c ∈ vinesV G, t = (twistedAtoms G Z.P c.atoms, coreBranchEquiv G Z.P c.upper,
        coreBranchEquiv G Z.P c.lower)} := by
  ext t
  constructor
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨c, hc, h1, h2, h3⟩ := Z.vinesV_preimage hc'
    exact ⟨c, hc, Prod.ext h1.symm (Prod.ext h2.symm h3.symm)⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c', hc', h1, h2, h3⟩ := Z.vinesV_image hc
    exact ⟨c', hc', Prod.ext h1.symm (Prod.ext h2.symm h3.symm)⟩

end TwistGroupSite
end WaveTurbulence.Stage1
