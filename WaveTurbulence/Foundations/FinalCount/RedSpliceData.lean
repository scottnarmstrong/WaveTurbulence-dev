/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceFinal
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): `g_sk` and `b_sk` (TARGET L1962, R19 (3))

The ingredient vines of the units of `𝒱_0`, the number of bad ones (`VineType.IsBad`: types (I), (II)), and the
total incoherency index of the vines of `𝒱_0` with respect to the pre-layering.  `g_sk` adds the incoherency
index `greg` of the attached regular couples and trees (REGRED data of the original garden, a parameter).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ}

/-- The vine ingredients of the units spliced for `σ` (the vines of `𝒱_0`). -/
def unitIngredients (G : Garden w) (σ : Prescription G) : Set (Finset (GBranch G.tree)) :=
  {T | ∃ u ∈ unitBlocks G σ, ∃ x y n p q, Vine.ChainIngredient G.molecule u.atoms x y n T p q}

/-- A vine of type (I) or (II). -/
def IsBadVineSet (G : Garden w) (T : Finset (GBranch G.tree)) : Prop :=
  ∃ X p q, X.IsBad = true ∧ G.molecule.IsVine X T p q

/-- `b_sk`: the number of bad vines among the ingredients of `𝒱_0`. -/
noncomputable def bskOf (G : Garden w) (σ : Prescription G) : ℕ :=
  (unitIngredients G σ ∩ {T | IsBadVineSet G T}).ncard

/-- The incoherency index of a vine (a chosen template realization; `0` for a non-vine). -/
noncomputable def vineIncoh (G : Garden w) (layer0 : GBranch G.tree → ℕ) (T : Finset (GBranch G.tree)) : ℕ := by
  classical
  exact if h : ∃ X p q, G.molecule.IsVine X T p q then
    Vine.realizedIncoherencyIndex
      (Classical.choice (Vine.isVine_iff_realization.mp h.choose_spec.choose_spec.choose_spec).2) layer0
  else 0

/-- `g_sk`: `greg` plus the total incoherency index of the vines of `𝒱_0`. -/
noncomputable def gskOf (greg : ℕ) (G : Garden w) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ) : ℕ :=
  greg + ∑ T ∈ (Set.toFinite (unitIngredients G σ)).toFinset, vineIncoh G layer0 T

end WaveTurbulence.RedSplice
