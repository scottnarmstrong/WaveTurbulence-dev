/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Shared.S1VInvMap` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvDesc
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso


/-!
# `𝒱` is equivariant along the unit twist (part 1: building blocks)

For a twist site inside a maximal group, the CL vines of the twisted garden correspond to those of the
original one; the root-VC test, the (CN) test and the top-ingredient test are transported.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem CLVineG.upper_mem {G : Garden w} (c : CLVineG γ G) : c.upper ∈ c.atoms := by
  have hX := c.isVine; exact (Src.isBlock_of_isSomeVine hX).2.1

theorem CLVineG.lower_mem {G : Garden w} (c : CLVineG γ G) : c.lower ∈ c.atoms := by
  have hX := c.isVine; exact (Src.isBlock_of_isSomeVine hX).2.2.1

theorem CLVineG.ext' {G : Garden w} {c d : CLVineG γ G} (h1 : c.atoms = d.atoms) (h2 : c.upper = d.upper)
    (h3 : c.lower = d.lower) : c = d := by
  cases c; cases d; simp_all

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite γ G)

/-- The image of a good CL vine under the unit twist. -/
@[expose] noncomputable def mapVine (c : CLVineG γ G) (hc : Z.Good c.atoms) : CLVineG γ Z.target where
  atoms := twistedAtoms G Z.P c.atoms
  upper := coreBranchEquiv G Z.P c.upper
  lower := coreBranchEquiv G Z.P c.lower
  isVine := MolIso.isSomeVine_img Z.iso c.isVine
  notParentUpper := fun h => c.notParentUpper ((Z.ip_map hc c.upper_mem).mp h)
  parentLower := (Z.ip_map hc c.lower_mem).mpr c.parentLower

/-- The pull-back of a CL vine of the twisted garden, if its atom set is good. -/
@[expose] noncomputable def pullVine (c : CLVineG γ Z.target) (hc : Z.Good (Z.iso.symm.img c.atoms)) :
    CLVineG γ G where
  atoms := Z.iso.symm.img c.atoms
  upper := Z.iso.symm.e c.upper
  lower := Z.iso.symm.e c.lower
  isVine := MolIso.isSomeVine_img Z.iso.symm c.isVine
  notParentUpper := by
    intro h
    have hv : Z.iso.symm.e c.upper ∈ Z.iso.symm.img c.atoms :=
      (Z.iso.symm.mem_img _ _).mpr c.upper_mem
    have h2 := (Z.ip_map hc hv).mpr h
    have e1 : twistedAtoms G Z.P (Z.iso.symm.img c.atoms) = c.atoms := Z.iso.img_symm_img _
    have e2 : coreBranchEquiv G Z.P (Z.iso.symm.e c.upper) = c.upper := Z.iso.e.apply_symm_apply _
    rw [e1, e2] at h2
    exact c.notParentUpper h2
  parentLower := by
    have hv : Z.iso.symm.e c.lower ∈ Z.iso.symm.img c.atoms :=
      (Z.iso.symm.mem_img _ _).mpr c.lower_mem
    have h2 := c.parentLower
    have e1 : twistedAtoms G Z.P (Z.iso.symm.img c.atoms) = c.atoms := Z.iso.img_symm_img _
    have e2 : coreBranchEquiv G Z.P (Z.iso.symm.e c.lower) = c.lower := Z.iso.e.apply_symm_apply _
    rw [← e1, ← e2] at h2
    exact (Z.ip_map hc hv).mp h2

/-- `IsCNVineG γ` is transported on good atom sets. -/
theorem cn_iff {T : Finset (GBranch G.tree)} (hT : Z.Good T) :
    IsCNVineG γ Z.target (twistedAtoms G Z.P T) ↔ IsCNVineG γ G T := by
  constructor
  · rintro ⟨a', b', hv, h1, h2⟩
    obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
    obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
    have hv' : Src.IsSomeVine γ G.molecule T a b := (MolIso.isSomeVine_img_iff Z.iso).mp hv
    have hX := hv'
    exact ⟨a, b, hX, fun h => h1 ((Z.ip_map hT (Src.isBlock_of_isSomeVine hX).2.1).mpr h),
      fun h => h2 ((Z.ip_map hT (Src.isBlock_of_isSomeVine hX).2.2.1).mpr h)⟩
  · rintro ⟨a, b, hv, h1, h2⟩
    have hX := hv
    exact ⟨coreBranchEquiv G Z.P a, coreBranchEquiv G Z.P b, MolIso.isSomeVine_img Z.iso hX,
      fun h => h1 ((Z.ip_map hT (Src.isBlock_of_isSomeVine hX).2.1).mp h), fun h => h2 ((Z.ip_map hT (Src.isBlock_of_isSomeVine hX).2.2.1).mp h)⟩

/-- `IsRootVCG γ` is transported on good atom sets. -/
theorem root_iff {S : Finset (GBranch G.tree)} (hS : Z.Good S) :
    IsRootVCG γ Z.target (twistedAtoms G Z.P S) ↔ IsRootVCG γ G S := by
  constructor
  · rintro ⟨a', b', hvc, hcl, hdeg⟩
    obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
    obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
    have hvc' : Src.IsVC γ G.molecule S a b := (MolIso.isVC_img_iff Z.iso).mp hvc
    have ha : a ∈ S := hvc'.1.2.1
    have hb : b ∈ S := hvc'.1.2.2.1
    refine ⟨a, b, hvc', ?_, ?_⟩
    · have ia := Z.ip_map hS ha
      have ib := Z.ip_map hS hb
      rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun h => h1 (ia.mpr h), ib.mp h2⟩
      · exact Or.inr ⟨fun h => h1 (ib.mpr h), ia.mp h2⟩
    · have h1 := Z.iso.deg_img a
      have h2 := Z.iso.deg_img b
      omega
  · rintro ⟨a, b, hvc, hcl, hdeg⟩
    have ha : a ∈ S := hvc.1.2.1
    have hb : b ∈ S := hvc.1.2.2.1
    refine ⟨coreBranchEquiv G Z.P a, coreBranchEquiv G Z.P b, MolIso.isVC_img Z.iso hvc, ?_, ?_⟩
    · have ia := Z.ip_map hS ha
      have ib := Z.ip_map hS hb
      rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun h => h1 (ia.mp h), ib.mpr h2⟩
      · exact Or.inr ⟨fun h => h1 (ib.mp h), ia.mpr h2⟩
    · have h1 : Z.target.molecule.deg (coreBranchEquiv G Z.P a) = G.molecule.deg a :=
        Z.iso.deg_img a
      have h2 : Z.target.molecule.deg (coreBranchEquiv G Z.P b) = G.molecule.deg b :=
        Z.iso.deg_img b
      omega

theorem InD_lower : Z.InD Z.P.lower := ⟨rfl, List.prefix_refl _⟩

/-- The upper joint of an ingredient is outside `S0`, or the upper joint of `S0`, or in the moved subtree. -/
theorem upper_ok {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) (c : CLVineG γ G)
    (hing : IsIngredientG γ G.molecule S c.atoms) :
    c.upper ∉ Z.S0 ∨ c.upper = Z.a0 ∨ Z.InD c.upper := by
  by_cases hu : c.upper ∈ Z.S0
  swap
  · exact Or.inl hu
  right
  by_cases hT : c.atoms = Z.S0
  · have hX := c.isVine
    have hd := (Mole.block_joint_degrees G.molecule (Src.isBlock_of_isSomeVine hX)).1
    rw [hT] at hd
    rcases block_degIn_cases Z.hB hu with ⟨hj, _⟩ | ⟨_, h4⟩
    · rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ Z.InD_lower)
    · omega
  · rcases Z.ing_joint hS hing hT hu c.upper_mem with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ Z.InD_lower)

theorem top_fwd {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) (c : CLVineG γ G)
    (hc : Z.Good c.atoms) (hing : IsIngredientG γ G.molecule S c.atoms)
    (hTop : IsTopIngredientG S c) :
    IsTopIngredientG (twistedAtoms G Z.P S) (Z.mapVine c hc) := by
  intro c'' hing'' hne''
  have hT_ing : IsIngredientG γ G.molecule S (Z.iso.symm.img c''.atoms) := by
    have h : IsIngredientG γ Z.target.molecule (Z.iso.img S) (Z.iso.img (Z.iso.symm.img c''.atoms)) := by
      rw [Z.iso.img_symm_img]; exact hing''
    exact (MolIso.isIngredient_img_iff Z.iso).mp h
  have hg := Z.ing_good hS hT_ing
  have hne' : (Z.pullVine c'' hg).atoms ≠ c.atoms := by
    intro h
    apply hne''
    have : Z.iso.img (Z.iso.symm.img c''.atoms) = Z.iso.img c.atoms := congrArg Z.iso.img h
    rw [Z.iso.img_symm_img] at this
    exact this
  obtain ⟨hup, hdesc⟩ := hTop (Z.pullVine c'' hg) hT_ing hne'
  have hc'' : c''.upper = coreBranchEquiv G Z.P (Z.pullVine c'' hg).upper :=
    (Z.iso.e.apply_symm_apply _).symm
  refine ⟨fun h => hup (Z.iso.e.injective (h.trans hc'')), ?_⟩
  rw [hc'']
  exact (Z.desc_map_iff' (Z.upper_ok hS c hing)).mp hdesc

theorem top_bwd {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule) (c : CLVineG γ G)
    (hc : Z.Good c.atoms) (hing : IsIngredientG γ G.molecule S c.atoms)
    (hTop : IsTopIngredientG (twistedAtoms G Z.P S) (Z.mapVine c hc)) :
    IsTopIngredientG S c := by
  intro c' hing' hne'
  have hg' := Z.ing_good hS hing'
  have hing'' : IsIngredientG γ Z.target.molecule (twistedAtoms G Z.P S) (Z.mapVine c' hg').atoms :=
    MolIso.isIngredient_img Z.iso hing'
  have hne'' : (Z.mapVine c' hg').atoms ≠ (Z.mapVine c hc).atoms := fun h =>
    hne' (Z.iso.img_injective h)
  obtain ⟨h1, h2⟩ := hTop _ hing'' hne''
  exact ⟨fun h => h1 (congrArg Z.iso.e h), (Z.desc_map_iff' (Z.upper_ok hS c hing)).mpr h2⟩

end TwistGroupSite
end WaveTurbulence.GammaLow.Fama
