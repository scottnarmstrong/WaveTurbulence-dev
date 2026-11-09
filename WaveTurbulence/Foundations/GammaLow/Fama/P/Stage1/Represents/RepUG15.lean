/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepUG15` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src` (by hand).
module
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.B.Fold8
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.VineA.VineUnitChain
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssemblyOf
public import WaveTurbulence.Foundations.Vine.B.Geom
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG15
import Mathlib.Tactic
/-! # The units' chain assemblies and their ingredient cover over `𝒱_γ` (main's `Represents` RepUG15)

`unitN σ j`: the number of ingredients of the chain of unit `j` (L5c's `unitBlocks_chainMk`); `unitAssembly hM σ j`:
its chain assembly over `𝒱_γ` (L5b's `clChainAssemblyΓ`), on main's CL region of the unit; `hcov_unitsMk`: every
unit ingredient is an ingredient (`IsIngredientG γ`) of its unit. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {S : Garden w} {γ : ℝ} [Fact (γ ≤ 1 / 2)]

/-- The number of ingredients of the chain of unit `j` (for the marked vine set `Mk`, inferred from `j`). -/
noncomputable def unitN (σ : Prescription S) {Mk : Set (CLVineG γ S)} (j : Fin (unitBlocks γ S σ Mk).length) : ℕ :=
  Classical.choose (Famc.VineA.unitBlocks_chainMk
    (List.get_mem _ _ : (unitBlocks γ S σ Mk).get j ∈ unitBlocks γ S σ Mk))

/-- The chain assembly over `𝒱_γ` of unit `j`, on main's CL region of the unit. -/
noncomputable def unitAssembly (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ S)}
    (j : Fin (unitBlocks γ S σ Mk).length) :
    Famb.VineEstS2.CLChainAssemblyΓ γ S (VineB.regionOf (unitBlkMk γ hM σ Mk j)) (unitN σ j) :=
  Famb.VineEstS2.clChainAssemblyΓ (Classical.choose_spec (Famc.VineA.unitBlocks_chainMk
    (List.get_mem _ _ : (unitBlocks γ S σ Mk).get j ∈ unitBlocks γ S σ Mk))) (unitBlkMk γ hM σ Mk j).isBlock
    (VineB.regionOf (unitBlkMk γ hM σ Mk j))

/-- Every unit ingredient is an ingredient of its unit (main's `hcov_unitsMk`). -/
theorem hcov_unitsMk (hM : S.molecule.IsMolecule) (σ : Prescription S) {Mk : Set (CLVineG γ S)} :
    ∀ T ∈ unitIngredients γ S σ Mk, ∃ j : Fin (unitBlocks γ S σ Mk).length,
      IsIngredientG γ S.molecule (unitBlkMk γ hM σ Mk j).atoms T := by
  rintro T ⟨u, hu, x, y, n, p, q, hi⟩
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
  have hc := (chainIngredientG_spec hi).1
  have hB := (unitBlkMk γ hM σ Mk j).isBlock
  have hj : ({x, y} : Finset (GBranch S.tree)) = {(unitBlkMk γ hM σ Mk j).upper, (unitBlkMk γ hM σ Mk j).lower} := by
    have hd := Mole.block_joint_degrees S.molecule hB
    exact Vine.joints_eq_of_two_low_degrees S.molecule (subset_refl _) hB.2.1 hB.2.2.1 hB.2.2.2.1
      (chain_joints_ne hc) (by omega) (by omega) (chain_interior_degree S.molecule hM hc)
  exact ⟨j, Or.inl ⟨x, y, n, p, q, Mole.block_transport_joints S.molecule hj hB, hi⟩⟩

/-- The unmarked form (main's `hcov_units`). -/
theorem hcov_units (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    ∀ T ∈ unitIngredients γ S σ, ∃ j : Fin (unitBlocks γ S σ).length,
      IsIngredientG γ S.molecule (unitBlk γ hM σ j).atoms T :=
  hcov_unitsMk (Mk := ∅) hM σ

end WaveTurbulence.GammaLow.Fama.Represents
