/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvDesc
import Mathlib.Tactic

/-!
# `𝒱` is equivariant along the unit twist (part 1: building blocks)

For a twist site inside a maximal group, the CL vines of the twisted garden correspond to those of the
original one; the root-VC test, the (CN) test and the top-ingredient test are transported.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

theorem CLVine.upper_mem {G : Garden w} (c : CLVine G) : c.upper ∈ c.atoms := by
  obtain ⟨X, hX⟩ := c.isVine; exact hX.1.2.1

theorem CLVine.lower_mem {G : Garden w} (c : CLVine G) : c.lower ∈ c.atoms := by
  obtain ⟨X, hX⟩ := c.isVine; exact hX.1.2.2.1

theorem CLVine.ext' {G : Garden w} {c d : CLVine G} (h1 : c.atoms = d.atoms) (h2 : c.upper = d.upper)
    (h3 : c.lower = d.lower) : c = d := by
  cases c; cases d; simp_all

namespace TwistGroupSite
variable {G : Garden w} (Z : TwistGroupSite G)

/-- The image of a good CL vine under the unit twist. -/
@[expose] noncomputable def mapVine (c : CLVine G) (hc : Z.Good c.atoms) : CLVine Z.target where
  atoms := twistedAtoms G Z.P c.atoms
  upper := coreBranchEquiv G Z.P c.upper
  lower := coreBranchEquiv G Z.P c.lower
  isVine := Z.iso.isSomeVine_img c.isVine
  notParentUpper := fun h => c.notParentUpper ((Z.ip_map hc c.upper_mem).mp h)
  parentLower := (Z.ip_map hc c.lower_mem).mpr c.parentLower

/-- The pull-back of a CL vine of the twisted garden, if its atom set is good. -/
@[expose] noncomputable def pullVine (c : CLVine Z.target) (hc : Z.Good (Z.iso.symm.img c.atoms)) :
    CLVine G where
  atoms := Z.iso.symm.img c.atoms
  upper := Z.iso.symm.e c.upper
  lower := Z.iso.symm.e c.lower
  isVine := Z.iso.symm.isSomeVine_img c.isVine
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

/-- `IsCNVine` is transported on good atom sets. -/
theorem cn_iff {T : Finset (GBranch G.tree)} (hT : Z.Good T) :
    IsCNVine Z.target (twistedAtoms G Z.P T) ↔ IsCNVine G T := by
  constructor
  · rintro ⟨a', b', hv, h1, h2⟩
    obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
    obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
    have hv' : IsSomeVine G.molecule T a b := Z.iso.isSomeVine_img_iff.mp hv
    obtain ⟨X, hX⟩ := hv'
    exact ⟨a, b, ⟨X, hX⟩, fun h => h1 ((Z.ip_map hT hX.1.2.1).mpr h),
      fun h => h2 ((Z.ip_map hT hX.1.2.2.1).mpr h)⟩
  · rintro ⟨a, b, hv, h1, h2⟩
    obtain ⟨X, hX⟩ := hv
    exact ⟨coreBranchEquiv G Z.P a, coreBranchEquiv G Z.P b, Z.iso.isSomeVine_img ⟨X, hX⟩,
      fun h => h1 ((Z.ip_map hT hX.1.2.1).mp h), fun h => h2 ((Z.ip_map hT hX.1.2.2.1).mp h)⟩

/-- `IsRootVC` is transported on good atom sets. -/
theorem root_iff {S : Finset (GBranch G.tree)} (hS : Z.Good S) :
    IsRootVC Z.target (twistedAtoms G Z.P S) ↔ IsRootVC G S := by
  constructor
  · rintro ⟨a', b', hvc, hcl, hdeg⟩
    obtain ⟨a, rfl⟩ := Z.iso.e.surjective a'
    obtain ⟨b, rfl⟩ := Z.iso.e.surjective b'
    have hvc' : IsVC G.molecule S a b := Z.iso.isVC_img_iff.mp hvc
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
    refine ⟨coreBranchEquiv G Z.P a, coreBranchEquiv G Z.P b, Z.iso.isVC_img hvc, ?_, ?_⟩
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
theorem upper_ok {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (c : CLVine G)
    (hing : IsIngredient G.molecule S c.atoms) :
    c.upper ∉ Z.S0 ∨ c.upper = Z.a0 ∨ Z.InD c.upper := by
  by_cases hu : c.upper ∈ Z.S0
  swap
  · exact Or.inl hu
  right
  by_cases hT : c.atoms = Z.S0
  · obtain ⟨X, hX⟩ := c.isVine
    have hd := (Mole.block_joint_degrees G.molecule hX.1).1
    rw [hT] at hd
    rcases block_degIn_cases Z.hB hu with ⟨hj, _⟩ | ⟨_, h4⟩
    · rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ Z.InD_lower)
    · omega
  · rcases Z.ing_joint hS hing hT hu c.upper_mem with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ Z.InD_lower)

theorem top_fwd {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (c : CLVine G)
    (hc : Z.Good c.atoms) (hing : IsIngredient G.molecule S c.atoms)
    (hTop : IsTopIngredient S c) :
    IsTopIngredient (twistedAtoms G Z.P S) (Z.mapVine c hc) := by
  intro c'' hing'' hne''
  have hT_ing : IsIngredient G.molecule S (Z.iso.symm.img c''.atoms) := by
    have h : IsIngredient Z.target.molecule (Z.iso.img S) (Z.iso.img (Z.iso.symm.img c''.atoms)) := by
      rw [Z.iso.img_symm_img]; exact hing''
    exact Z.iso.isIngredient_img_iff.mp h
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

theorem top_bwd {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (c : CLVine G)
    (hc : Z.Good c.atoms) (hing : IsIngredient G.molecule S c.atoms)
    (hTop : IsTopIngredient (twistedAtoms G Z.P S) (Z.mapVine c hc)) :
    IsTopIngredient S c := by
  intro c' hing' hne'
  have hg' := Z.ing_good hS hing'
  have hing'' : IsIngredient Z.target.molecule (twistedAtoms G Z.P S) (Z.mapVine c' hg').atoms :=
    Z.iso.isIngredient_img hing'
  have hne'' : (Z.mapVine c' hg').atoms ≠ (Z.mapVine c hc).atoms := fun h =>
    hne' (Z.iso.img_injective h)
  obtain ⟨h1, h2⟩ := hTop _ hing'' hne''
  exact ⟨fun h => h1 (congrArg Z.iso.e h), (Z.desc_map_iff' (Z.upper_ok hS c hing)).mpr h2⟩

end TwistGroupSite
end WaveTurbulence.Stage1
