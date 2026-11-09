/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVMissingJoint`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`: `σ(a, b) = 1` and two members of `𝒱_{γL}` sharing exactly their joints), whose branches are T-vines
(`H/DS/DV.lean`). Low-range change: the branches are members of the low family with `σ = 1` (hypotheses `hσ`, `Src.IsSomeVine Src.γL`;
main: two vines (V)); main's `DV_missing_joint_side` is `DS.DV_missing_joint_side_blocks` (block branches).

# Objects missing a DV′ joint lie in one branch -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, ordinary inner VC in a DV′ missing either joint: its endpoint-removal connectivity localizes it in one
branch. -/
theorem VC_in_DV_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hσ : M.sigma a b = 1) (hS : Src.IsSomeVine Src.γL M S a b)
    (hT : Src.IsSomeVine Src.γL M T a b) (hi : S ∩ T = {a, b}) (hA : Src.IsVC Src.γL M A x y) (hAU : A ⊆ S ∪ T)
    (hmiss : ¬(a ∈ A ∧ b ∈ A)) : A ⊆ S ∨ A ⊆ T := by
  have hd := DS.dv_degree_profile hM hσ hS.block hT.block hi
  apply DS.DV_missing_joint_side_blocks hM hS.block hT.block hAU hmiss
  intro z hz
  by_cases hzA : z ∈ A
  · have hdz : M.degIn (S ∪ T) z = 3 := hz.elim (fun h => h.symm ▸ hd.1) (fun h => h.symm ▸ hd.2.1)
    have hle := degIn_mono M hAU z
    have hzj : z = x ∨ z = y := by
      by_contra hh
      have h4 := hA.1.2.2.2.2.2.2.2.2.1 z hzA (not_or.mp hh).1 (not_or.mp hh).2
      omega
    exact isVC_erase_joint_connected hA hzj
  · rw [Finset.erase_eq_self.mpr hzA]
    exact isVC_connected hA

/-- Every contained HV/HVC missing a DV′ joint likewise lies in one branch. -/
theorem hyperLike_in_DV_missing_joint_side (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hS : Src.IsSomeVine Src.γL M S a b) (hT : Src.IsSomeVine Src.γL M T a b)
    (hA : Src.IsHV Src.γL M A x y ∨ Src.IsHVC Src.γL M A x y) (hAU : A ⊆ S ∪ T)
    (hmiss : ¬(a ∈ A ∧ b ∈ A)) : A ⊆ S ∨ A ⊆ T :=
  DS.DV_missing_joint_side_blocks hM hS.block hT.block hAU hmiss (fun z _hz => hyperLike_erase_connected M hA z)

end WaveTurbulence.GammaLow.FinalCount.H
