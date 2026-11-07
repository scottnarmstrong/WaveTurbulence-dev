/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepUG14
public import WaveTurbulence.Foundations.Vine.A.VineUnitChain
public import WaveTurbulence.Foundations.Vine.A.VineIngredientCarrier
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, step 4 instantiation: chain assemblies of the units and `hcov`

* `unitN`, `unitAssembly`: for every unit `j` of `unitBlocks S σ` a `CLChainAssembly S (regionOf (unitBlk j)) (unitN j)` from VINE-A's
  `unitBlocks_chain` (an actual chain in the CL joint order) and V5's `clChainAssembly`;
* `hcov_units`: every ingredient of the units (`unitIngredients S σ`) is an ingredient of the block of some unit `j` (the input
  `hcov` of `sum_vineIncoh_le_cohmol`, `card_bad_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA

variable {w : ℕ} {S : Garden w}

/-- The number of ingredients of the chain of unit `j`. -/
noncomputable def unitN (σ : Prescription S) (j : Fin (unitBlocks S σ).length) : ℕ :=
  Classical.choose (WaveTurbulence.VineA.unitBlocks_chain (G := S) (σ := σ) (List.get_mem _ _ : (unitBlocks S σ).get j ∈ unitBlocks S σ))

/-- The chain assembly of unit `j`. -/
noncomputable def unitAssembly (hM : S.molecule.IsMolecule) (σ : Prescription S) (j : Fin (unitBlocks S σ).length) :
    CLChainAssembly S (regionOf (unitBlk hM σ j)) (unitN σ j) :=
  clChainAssembly (Classical.choose_spec (WaveTurbulence.VineA.unitBlocks_chain (G := S) (σ := σ)
    (List.get_mem _ _ : (unitBlocks S σ).get j ∈ unitBlocks S σ))) (unitBlk hM σ j).isBlock (regionOf (unitBlk hM σ j))

theorem hcov_units (hM : S.molecule.IsMolecule) (σ : Prescription S) :
    ∀ T ∈ unitIngredients S σ, ∃ j : Fin (unitBlocks S σ).length, IsIngredient S.molecule (unitBlk hM σ j).atoms T := by
  rintro T ⟨u, hu, x, y, n, p, q, hi⟩
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hu
  have hj := chain_block_joints (Mole.garden_isMolecule S) (unitBlk hM σ j).isBlock (Vine.chainIngredient_spec hi).1
  have hB := Mole.block_transport_joints S.molecule hj (unitBlk hM σ j).isBlock
  exact ⟨j, Or.inl ⟨x, y, n, p, q, hB, hi⟩⟩

end WaveTurbulence.Represents
