/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
/-! # `DV′`: degrees and missing-joint localization (packet L5c)

Main's `Molecule/VineDVDegrees.lean` (`isDV_degree_profile`) and `Molecule/VineDVMissingJoint.lean`
(`DV_missing_joint_side`, `VC_in_DV_missing_joint_side`), sha256 in `COPIED-SHA256SUMS`, for `DV′` (D11
`IsDVPrime`: two members of `𝒱_γ` with `σ = 1` sharing exactly both joints) instead of two vines (V). Main uses of
type (V) only `σ = 1` (through `isVine_joint_pair_degrees`) and the block structure; here `σ = 1` is part of `DV′`,
and `degIn {a, b} a = σ` holds for any block joint (no loop at a joint, `degIn_pair_eq_bondsBetween`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.Vine (GroupConnected degIn_union_inter degIn_mono two_groups_missing_right_joint_side)

variable {γv : ℝ} {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- At a joint of a block, the internal degree in the pair of joints is `σ`. -/
theorem block_degIn_pair_eq_sigma {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    M.degIn {a, b} a = M.sigma a b := by
  apply Mole.degIn_pair_eq_bondsBetween M hB.2.2.2.1
  intro x hxa hxm
  -- a dart from `a` to `a` with `a ∈ S` is internal to `S`; a block joint carries no loop
  exact LGSpine.block_joint_no_loop hB hxa hxm ⟨hxa ▸ hB.2.1, hxm ▸ hB.2.1⟩

/-- **`DV′` degree profile** (main `isDV_degree_profile`): degree-three joints, degree-four interior atoms. -/
theorem isDVPrime_degree_profile (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b : V} (hS : IsSomeVine γv M S a b) (hT : IsSomeVine γv M T a b)
    (hσ : M.sigma a b = 1) (hi : S ∩ T = {a, b}) :
    M.degIn (S ∪ T) a = 3 ∧ M.degIn (S ∪ T) b = 3 ∧
      ∀ v ∈ S ∪ T, v ≠ a → v ≠ b → M.degIn (S ∪ T) v = 4 := by
  have hSB := isBlock_of_isSomeVine hS
  have hTB := isBlock_of_isSomeVine hT
  have hs := Mole.block_joint_degrees M hSB
  have ht := Mole.block_joint_degrees M hTB
  have hpa : M.degIn {a, b} a = 1 := (block_degIn_pair_eq_sigma hSB).trans hσ
  have hpb : M.degIn {a, b} b = 1 := by
    have h := block_degIn_pair_eq_sigma (Mole.block_swap_joints M hSB)
    rw [Finset.pair_comm, sigma_comm] at h
    exact h.trans hσ
  have hda := degIn_union_inter M S T a hSB.2.1 hTB.2.1
  have hdb := degIn_union_inter M S T b hSB.2.2.1 hTB.2.2.1
  rw [hi, hpa, hs.1, ht.1] at hda
  rw [hi, hpb, hs.2, ht.2] at hdb
  refine ⟨by omega, by omega, ?_⟩
  intro v hv hva hvb
  have hvm : v ∈ M.atoms := (union_subset hSB.1 hTB.1) hv
  have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvm)
  rcases mem_union.mp hv with hv | hv
  · have hd := hSB.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
    omega
  · have hd := hTB.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
    omega

/-- Primitive two-joint separator localization in the two constituents of a `DV′` (main `DV_missing_joint_side`). -/
theorem DVPrime_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b : V} (hS : IsSomeVine γv M S a b) (hT : IsSomeVine γv M T a b)
    (hAU : A ⊆ S ∪ T) (hmiss : ¬(a ∈ A ∧ b ∈ A))
    (hconn : ∀ z, z = a ∨ z = b → GroupConnected M (A.erase z)) : A ⊆ S ∨ A ⊆ T := by
  have hSB := isBlock_of_isSomeVine hS
  have hTB := isBlock_of_isSomeVine hT
  by_cases hb : b ∈ A
  · have ha : a ∉ A := fun ha => hmiss ⟨ha, hb⟩
    exact two_groups_missing_right_joint_side M hM S T A b a hSB.2.2.1 hTB.2.2.1
      hSB.2.2.2.1.symm hTB.1
      (fun v hv hvb hva => hTB.2.2.2.2.2.2.2.2.1 v hv hva hvb) hAU ha (hconn b (Or.inr rfl))
  · exact two_groups_missing_right_joint_side M hM S T A a b hSB.2.1 hTB.2.1
      hSB.2.2.2.1 hTB.1 hTB.2.2.2.2.2.2.2.2.1 hAU hb (hconn a (Or.inl rfl))

/-- A `𝒱_γ` VC stays connected after deleting one of its joints (main `isVC_erase_joint_connected`). -/
theorem isVC_erase_joint_connected (hfam : FamFacts γv) {M : Molecule V D} {S : Finset V} {a b z : V}
    (h : IsVC γv M S a b) (hz : z = a ∨ z = b) : GroupConnected M (S.erase z) := by
  obtain ⟨_hB, n, hchain⟩ := h
  rcases hz with hz | hz
  · rw [hz]
    exact chain_erase_first_connected hfam hchain
  · rw [hz]
    exact chain_erase_first_connected hfam (chain_swap hchain)

/-- **TARGET subsetvc** for an ordinary `𝒱_γ` VC inside a `DV′` missing either joint: it lies in one constituent
(main `VC_in_DV_missing_joint_side`). -/
theorem VC_in_DVPrime_missing_joint_side (hfam : FamFacts γv) (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hS : IsSomeVine γv M S a b) (hT : IsSomeVine γv M T a b)
    (hσ : M.sigma a b = 1) (hi : S ∩ T = {a, b}) (hA : IsVC γv M A x y) (hAU : A ⊆ S ∪ T)
    (hmiss : ¬(a ∈ A ∧ b ∈ A)) : A ⊆ S ∨ A ⊆ T := by
  have hd := isDVPrime_degree_profile M hM hS hT hσ hi
  apply DVPrime_missing_joint_side M hM hS hT hAU hmiss
  intro z hz
  by_cases hzA : z ∈ A
  · have hdz : M.degIn (S ∪ T) z = 3 := hz.elim (fun h => h.symm ▸ hd.1) (fun h => h.symm ▸ hd.2.1)
    have hle := degIn_mono M hAU z
    have hzj : z = x ∨ z = y := by
      by_contra hh
      have h4 := hA.1.2.2.2.2.2.2.2.2.1 z hzA (not_or.mp hh).1 (not_or.mp hh).2
      omega
    exact isVC_erase_joint_connected hfam hA hzj
  · rw [Finset.erase_eq_self.mpr hzA]
    exact isVC_connected hA

end WaveTurbulence.GammaLow.Famc
