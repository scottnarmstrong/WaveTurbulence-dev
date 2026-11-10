/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClass
public import WaveTurbulence.Foundations.Flower.MkUnitsL.Defs

/-! # B3s-HELPER5 (γ) T2: the unit top filters of a class (`MkUnitsL.UnitTopFilters`)

B3-2's `UnitTopFilters L p a Mk SU base roots E` asks for a top weight `E` that is a function of the layered garden
and equals, on the reconstruction of every member `y` of the run class, the product over the units of the top
filters at radii `SU j` read at the member's unit top `(y.2 j).blk.a` on the collapsed decoration.

* `stemPick LG J t dd`: the capped-stem branch of tree `t` at depth `dd` (unique with one capped flower per tree,
  δ's `MkSlotsS.stem_eq_of_length`); `stemPick_eq`;
* `topE`: the product, over the units `j`, of the filters `radProd (SU j)` at `stemPick LG J (tj j) (dj j)`;
* **`unitTopFilters_stem`**: with `SU := SUStem` (tree-indexed radii, e.g. σ's) and `(tj j, dj j)` the tree and depth
  of the representative's core of the upper joint of unit `j`, `UnitTopFilters` holds at the marked set `mk a.prime`
  (B4's `classMk mkF a` at the integration's marking): the member's unit top is a stem node exactly when the
  representative's is (`stemB_member_iff`), in the same tree and at the same depth (δ's
  `MkSlotsS.stemCore_length_member`), so it is the picked node, and its filter is the member's top filter
  (`radProd_core_eq_nodeWeight`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt)

namespace WaveTurbulence.Flower.MkSlotsT

section Class
variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (J : Finset (Fin (2 * R)))

/-- The tree of the representative's core of the upper joint of unit `j`. -/
def topTree (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : Fin (2 * R) :=
  (a.prime.data.corePosition (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper).1

/-- The representative's unit radius lists for tree-indexed radii. -/
abbrev SURep (radT : Fin (2 * R) → List ℝ) :
    Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ :=
  SUStem a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (fun b => radT b.1.1)
    (blk := unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))

end Class

end WaveTurbulence.Flower.MkSlotsT
