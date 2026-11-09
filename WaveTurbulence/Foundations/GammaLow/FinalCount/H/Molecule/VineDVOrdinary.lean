/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVOrdinary
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCInTypeV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVOrdinary`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`: `σ(a, b) = 1` and two members of `𝒱_{γL}` sharing exactly their joints), whose branches are T-vines
(`H/DS/DV.lean`). Low-range change: a block of a DV′ containing both joints is a T-vine (main: a vine (V)); the third alternative of
`VC_in_DV` is a T-vine (N3 Cor 1.16′(2) in a branch, `VC_in_TVine`).

# VCs in a DV′ -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, both-joints DV′ case: any contained ordinary block containing both joints is one of the branches,
a T-vine. -/
theorem block_in_DV_both_joints_isTVine (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : Src.IsDV Src.γL M U a b) (hA : M.IsBlock A x y)
    (hAU : A ⊆ U) (ha : a ∈ A) (hb : b ∈ A) : M.IsTVine A x y := by
  obtain ⟨S, T, hσ, hS, hT, hi, rfl⟩ := DS.dv_branches hU
  rcases DS.block_in_DV_both_joints_eq_branchL hM hσ hS hT hi hA hAU ha hb with rfl | rfl
  · exact DS.isTVine_rejoint hS hA
  · exact DS.isTVine_rejoint hT hA

/-- TARGET Lemma subsetvc, complete ordinary inner-VC classification in a DV′ of the low family: one or two double
bonds or a T-vine. No decoration or gap hypothesis. -/
theorem VC_in_DV (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V} (hU : Src.IsDV Src.γL M U a b) (hA : Src.IsVC Src.γL M A x y) (hAU : A ⊆ U) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  by_cases hboth : a ∈ A ∧ b ∈ A
  · exact Or.inr (Or.inr (block_in_DV_both_joints_isTVine M hM hU hA.1 hAU hboth.1 hboth.2))
  · obtain ⟨hσ, S, T, hS, hT, hi, rfl⟩ := hU
    rcases VC_in_DV_missing_joint_side M hM hσ hS hT hi hA hAU hboth with hAS | hAT
    · exact VC_in_TVine M (DS.isTVine_of_sigma_one hS hσ) hA hAS
    · exact VC_in_TVine M (DS.isTVine_of_sigma_one hT hσ) hA hAT

end WaveTurbulence.GammaLow.FinalCount.H
