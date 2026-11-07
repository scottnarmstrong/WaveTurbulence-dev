/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
public import WaveTurbulence.Foundations.FinalCount.RedSpliceResidual
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): the spliced skeleton `G_sb` and its merge labelling

`stSt G σ`: the simultaneous splice (`spliceFold`) of all units of `unitBlocks G σ`.  The merge labelling
`cls` is the crown on the atoms of a unit and `none` elsewhere.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ}

/-- The splice state of the skeleton `G` for the prescription `σ`. -/
@[expose] noncomputable def stSt (G : Garden w) (σ : Prescription G) : SpState G :=
  spliceFold G (unitBlocks G σ)

/-- **`𝒢_sb`**: the skeleton with all units of `𝒱_0` spliced (TARGET L1953-L1955). -/
@[expose] noncomputable def gsbOf (G : Garden w) (σ : Prescription G) : Garden w := (stSt G σ).G

section cls
variable {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

theorem stSt_cls_mem {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    (stSt G σ).cls v = some u.upper :=
  spliceFold_cls_mem (unitBlocks G σ) (unitBlocks_pairwise hM σ) hu hv

theorem stSt_cls_none {v : GBranch G.tree} (hv : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms) :
    (stSt G σ).cls v = none :=
  spliceFold_cls_notMem (unitBlocks G σ) (unitBlocks_pairwise hM σ) hv

theorem stSt_repC_mem {u : CLBlock G} (hu : u ∈ unitBlocks G σ) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    repC (stSt G σ).cls v = u.upper := by
  simp [repC, stSt_cls_mem hM σ hu hv]

theorem stSt_repC_none {v : GBranch G.tree} (hv : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms) :
    repC (stSt G σ).cls v = v := by
  simp [repC, stSt_cls_none hM σ hv]

end cls

end WaveTurbulence.RedSplice
