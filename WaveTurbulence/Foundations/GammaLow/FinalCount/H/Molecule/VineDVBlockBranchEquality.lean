/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVBlockBranchEquality
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVBlockBranchEquality`** (sha256 in H/COPIED-SHA256SUMS), **restated over the
low family by L6-HDS** (PLAN-L6 §3e–3f, layer H-DS). Main's DV is two vines (V); here it is the DV′ of D11
(`Src.IsDV Src.γL`: `σ(a, b) = 1` and two members of `𝒱_{γL}` sharing exactly their joints), whose branches are T-vines
(`H/DS/DV.lean`). Low-range change: the branches are T-vines with `σ = 1` (main: vines (V)); the proof is `DS.block_in_DV_both_joints_eq_branchL`
(interior connectivity of a T-vine: N2 Thm 1.15 (F1), `Src.DSInputs`).

# A block of a DV′ containing both joints is a branch -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The both-joints DV′ block proof identifies an actual branch atom set. This equality is used for removals. -/
theorem block_in_DV_both_joints_eq_branch (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b x y : V} (hσ : M.sigma a b = 1) (hS : M.IsTVine S a b) (hT : M.IsTVine T a b)
    (hi : S ∩ T = {a, b}) (hA : M.IsBlock A x y) (hAU : A ⊆ S ∪ T)
    (ha : a ∈ A) (hb : b ∈ A) : A = S ∨ A = T :=
  DS.block_in_DV_both_joints_eq_branchL hM hσ hS hT hi hA hAU ha hb

end WaveTurbulence.GammaLow.FinalCount.H
