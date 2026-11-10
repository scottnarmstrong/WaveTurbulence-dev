/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Shared.S1VInvEquiv` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso


/-!
# `𝒱` is equivariant along the unit twist (TARGET `defcong`, L1934-L1937)

For a unit twist at a vine of a maximal group, `vinesVG γ` of the twisted skeleton is the image of `vinesVG γ`
of the original skeleton along `unitTwistDirectedIso` (vines are matched by atoms, upper and lower joint).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite γ G)

/-- The membership condition of `vinesVG γ` for a fixed group. -/
@[expose] def Cond {G : Garden w} (γ : ℝ) [Fact (γ ≤ 1 / 2)] (S : Finset (GBranch G.tree)) (c : CLVineG γ G) : Prop :=
  (∃ a b, Src.IsVC γ G.molecule S a b ∧ ¬ IsRootVCG γ G S) ∨
    ((∃ a b, Src.IsHVC γ G.molecule S a b) ∨ IsRootVCG γ G S) ∧
      ((∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T) ∨ ¬ IsTopIngredientG S c)

theorem cond_iff {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) (c : CLVineG γ G)
    (hc : Z.Good c.atoms) (hing : IsIngredientG γ G.molecule S c.atoms) :
    Cond γ S c ↔ Cond γ (twistedAtoms G Z.P S) (Z.mapVine c hc) := by
  have hSg := Z.group_good hS
  have hvc : (∃ a b, Src.IsVC γ G.molecule S a b) ↔
      ∃ a b, Src.IsVC γ Z.target.molecule (twistedAtoms G Z.P S) a b := by
    constructor
    · rintro ⟨a, b, h⟩; exact ⟨_, _, MolIso.isVC_img Z.iso h⟩
    · rintro ⟨a', b', h⟩
      obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
      obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
      exact ⟨a, b, (MolIso.isVC_img_iff Z.iso).mp h⟩
  have hhvc : (∃ a b, Src.IsHVC γ G.molecule S a b) ↔
      ∃ a b, Src.IsHVC γ Z.target.molecule (twistedAtoms G Z.P S) a b := by
    constructor
    · rintro ⟨a, b, h⟩; exact ⟨_, _, MolIso.isHVC_img Z.iso h⟩
    · rintro ⟨a', b', h⟩
      obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
      obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
      exact ⟨a, b, (MolIso.isHVC_img_iff Z.iso).mp h⟩
  have hcn : (∃ T, IsIngredientG γ G.molecule S T ∧ IsCNVineG γ G T) ↔
      ∃ T', IsIngredientG γ Z.target.molecule (twistedAtoms G Z.P S) T' ∧ IsCNVineG γ Z.target T' := by
    constructor
    · rintro ⟨T, hT, hcn⟩
      exact ⟨twistedAtoms G Z.P T, MolIso.isIngredient_img Z.iso hT, (Z.cn_iff (Z.ing_good hS hT)).mpr hcn⟩
    · rintro ⟨T', hT', hcn'⟩
      have hT : IsIngredientG γ G.molecule S (Z.iso.symm.img T') := by
        have h : IsIngredientG γ Z.target.molecule (Z.iso.img S) (Z.iso.img (Z.iso.symm.img T')) := by
          rw [Z.iso.img_symm_img]; exact hT'
        exact (MolIso.isIngredient_img_iff Z.iso).mp h
      refine ⟨_, hT, (Z.cn_iff (Z.ing_good hS hT)).mp ?_⟩
      have e1 : twistedAtoms G Z.P (Z.iso.symm.img T') = T' := Z.iso.img_symm_img _
      rw [e1]; exact hcn'
  have htop : IsTopIngredientG S c ↔
      IsTopIngredientG (twistedAtoms G Z.P S) (Z.mapVine c hc) :=
    ⟨Z.top_fwd hS c hc hing, Z.top_bwd hS c hc hing⟩
  have hroot := Z.root_iff hSg
  unfold Cond
  simp only [exists_and_right, hvc, hhvc, hcn, htop, hroot]

/-- Membership in `𝒱` is transported (forward). -/
theorem mapVine_mem {c : CLVineG γ G} (hc : c ∈ vinesVG γ G) :
    ∃ hg : Z.Good c.atoms, Z.mapVine c hg ∈ vinesVG γ Z.target := by
  obtain ⟨S, hS, hing, hcond⟩ := hc
  have hg := Z.ing_good hS hing
  refine ⟨hg, twistedAtoms G Z.P S, MolIso.maximalGroups_img Z.iso hS, MolIso.isIngredient_img Z.iso hing, ?_⟩
  exact (Z.cond_iff hS c hg hing).mp hcond

/-- **Equivariance of `𝒱` (image)**: every vine of `𝒱` is carried to a vine of `𝒱` of the twisted
skeleton, with image atoms and joints. -/
theorem vinesV_image {c : CLVineG γ G} (hc : c ∈ vinesVG γ G) :
    ∃ c' ∈ vinesVG γ Z.target, c'.atoms = twistedAtoms G Z.P c.atoms ∧
      c'.upper = coreBranchEquiv G Z.P c.upper ∧ c'.lower = coreBranchEquiv G Z.P c.lower := by
  obtain ⟨hg, hm⟩ := Z.mapVine_mem hc
  exact ⟨_, hm, rfl, rfl, rfl⟩

/-- **Equivariance of `𝒱` (preimage)**: every vine of `𝒱` of the twisted skeleton comes from a vine
of `𝒱` of the original skeleton. -/
theorem vinesV_preimage {c' : CLVineG γ Z.target} (hc : c' ∈ vinesVG γ Z.target) :
    ∃ c ∈ vinesVG γ G, twistedAtoms G Z.P c.atoms = c'.atoms ∧
      coreBranchEquiv G Z.P c.upper = c'.upper ∧ coreBranchEquiv G Z.P c.lower = c'.lower := by
  obtain ⟨S', hS', hing', hcond'⟩ := hc
  have hS : Z.iso.symm.img S' ∈ maximalGroupsG γ G.molecule := by
    have h : Z.iso.img (Z.iso.symm.img S') ∈ maximalGroupsG γ Z.target.molecule := by
      rw [Z.iso.img_symm_img]; exact hS'
    exact (MolIso.maximalGroups_img_iff Z.iso).mp h
  have hing : IsIngredientG γ G.molecule (Z.iso.symm.img S') (Z.iso.symm.img c'.atoms) := by
    have h : IsIngredientG γ Z.target.molecule (Z.iso.img (Z.iso.symm.img S'))
        (Z.iso.img (Z.iso.symm.img c'.atoms)) := by
      rw [Z.iso.img_symm_img, Z.iso.img_symm_img]; exact hing'
    exact (MolIso.isIngredient_img_iff Z.iso).mp h
  have hg := Z.ing_good hS hing
  set c := Z.pullVine c' hg with hcdef
  have hmc : Z.mapVine c hg = c' := by
    apply CLVineG.ext'
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


end TwistGroupSite
end WaveTurbulence.GammaLow.Fama
