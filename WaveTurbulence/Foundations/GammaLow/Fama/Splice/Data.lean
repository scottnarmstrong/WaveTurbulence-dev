/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceData` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceData


/-!
# REDSPLICE-DEF (S2a): `g_sk` and `b_sk` (TARGET L1962, R19 (3))

The ingredient vines of the units of `𝒱_0`, the number of bad ones (`VineType.IsBad`: types (I), (II)), and the
total incoherency index of the vines of `𝒱_0` with respect to the pre-layering.  `g_sk` adds the incoherency
index `greg` of the attached regular couples and trees (REGRED data of the original garden, a parameter).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The vine ingredients of the units spliced for `σ` (the vines of `𝒱_0`). -/
def unitIngredients (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : Set (Finset (GBranch G.tree)) :=
  {T | ∃ u ∈ unitBlocks γ G σ Mk, ∃ x y n p q, ChainIngredientG γ G.molecule u.atoms x y n T p q}

/-- `b_sk`: the number of bad vines among the ingredients of `𝒱_0`. -/
noncomputable def bskOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : ℕ :=
  (unitIngredients γ G σ Mk ∩ {T | RedSplice.IsBadVineSet G T}).ncard

/-- The incoherency index of a vine of `𝒱_γ` (TARGET Def `cohmol`, L1489–L1499): the number of its groups that are
not contained in one layer. For a bad vine (I), (II) the groups are main's template groups (a chosen realization,
`Vine.realizedIncoherencyIndex`, as main); for a T-vine they are its pieces (D11 `Molecule.tvineGroups`, N3 §4.2:
"groups := 2-cut pieces", REFEREED REF3), which are intrinsic, so no realization is chosen. `0` for a non-vine. -/
noncomputable def vineIncoh (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (layer0 : GBranch G.tree → ℕ)
    (T : Finset (GBranch G.tree)) : ℕ := by
  classical
  exact if h : ∃ X p q, X.IsBad = true ∧ G.molecule.IsVine X T p q then
    Vine.realizedIncoherencyIndex
      (Classical.choice (Vine.isVine_iff_realization.mp h.choose_spec.choose_spec.choose_spec.2).2) layer0
  else if h' : ∃ p q, G.molecule.IsTVine T p q then
    Vine.incoherencyIndex layer0
      ((G.molecule.tvineGroups T h'.choose h'.choose_spec.choose).toList.map Finset.toList)
  else 0

/-- `g_sk`: `greg` plus the total incoherency index of the vines of `𝒱_0`. -/
noncomputable def gskOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (greg : ℕ) (G : Garden w) (σ : Prescription G) (layer0 : GBranch G.tree → ℕ)
    (Mk : Set (CLVineG γ G) := ∅) : ℕ :=
  greg + ∑ T ∈ (Set.toFinite (unitIngredients γ G σ Mk)).toFinset, vineIncoh γ G layer0 T

end WaveTurbulence.GammaLow.Fama
