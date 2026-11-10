/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeSlots
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalize
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChartNormalizeGroups
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafCount
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
public import WaveTurbulenceVineParam.VineParamGrouped

/-! # Visible consumption of the named full-vine obligation -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open TTree RegRed VineParamContract
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A fixed realization of a molecule vine (its cohmol groups are intrinsic, `realizedGroupSets_eq`). -/
noncomputable def chosenRealization {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (hV : M.IsVine X S a b) : WaveTurbulence.Vine.VineRealization M X S a b :=
  Classical.choice (WaveTurbulence.Vine.isVine_iff_realization.mp hV).2

/-- The molecule theorem is applied to the actual garden molecule and current connected IsVine; since R22 the chart
is taken from the proved `vineparam_grouped` (chart groups = cohmol groups of `chosenRealization`), so `hM9` is vestigial. -/
noncomputable def chosenVineChart (_hM9 : VINEPARAM) (X : VineType)
    (hV : G.molecule.IsVine X U a b) : FullVineChart G.molecule X U a b :=
  normalizeChart (Classical.choose (WaveTurbulence.Vine.Param.vineparam_grouped _ _ G.molecule
    (Mole.garden_isMolecule G) X U a b hV (chosenRealization hV)))

/-- M9's source atom indexing gives exactly the number of interior garden
branches, without a separate cardinality assumption. -/
theorem vineChart_dimension {X : VineType} (R : CLRegionData G U a b)
    (A : FullVineChart G.molecule X U a b) : A.indexing.shape.n = clLocalOrder1 R := by
  change A.indexing.shape.n = (U.erase a).card
  have hc := Fintype.card_congr A.indexing.atom
  simpa only [Fintype.card_fin,Fintype.card_coe] using hc

end WaveTurbulence.VineEstS2
