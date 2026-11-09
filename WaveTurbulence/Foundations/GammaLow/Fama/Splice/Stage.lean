/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceStage` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.FinalCount.RedSpliceResidual
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage


/-!
# REDSPLICE-DEF (S2a): the spliced skeleton `G_sb` and its merge labelling

`stSt γ G σ`: the simultaneous splice (`spliceFold`) of all units of `unitBlocks γ G σ`.  The merge labelling
`cls` is the crown on the atoms of a unit and `none` elsewhere.  B1a: `stSt γ G σ Mk`, `gsbOf γ G σ Mk` take the trailing
marked vine set (default `∅`); `stStMk` (probe name) and the `∅`-bridges are added.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)]

/-- The splice state of the skeleton `G` for the prescription `σ`.  B1a: with the marked vine set `Mk` (default `∅`)
the runs of the marked groups are spliced (o75's `𝒢_sb`). -/
@[expose] noncomputable def stSt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : SpState G :=
  spliceFold G (unitBlocks γ G σ Mk)

/-- **`𝒢_sb`**: the skeleton with all units of `𝒱_0` spliced (TARGET L1953-L1955). -/
@[expose] noncomputable def gsbOf (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G) := ∅) : Garden w :=
  (stSt γ G σ Mk).G

/-- The Stage-1′ splice state `G_sb` (runs spliced; copied by source from the B0 probe, lines 187–190). -/
noncomputable def stStMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) : SpState G :=
  spliceFold G (unitBlocksMk γ G σ Mk)

theorem stStMk_eq (G : Garden w) (σ : Prescription G) (Mk : Set (CLVineG γ G)) :
    stStMk γ G σ Mk = stSt γ G σ Mk := rfl

theorem stStMk_empty (G : Garden w) (σ : Prescription G) : stStMk γ G σ ∅ = stSt γ G σ := by
  simp only [stStMk, stSt, unitBlocksMk_empty]

/-- B1a bridge: at `Mk = ∅` the splice state is the fold of main's units. -/
theorem stSt_empty (G : Garden w) (σ : Prescription G) :
    stSt γ G σ = spliceFold G ((sgGroups γ G σ).flatMap (fun S => (groupUnitsOf γ G S).units)) := by
  unfold stSt
  rw [unitBlocks_empty]

section clsMk
variable {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G) (Mk : Set (CLVineG γ G))
include hM

/-- B1a: `stSt_cls_mem` for every marked vine set. -/
theorem stSt_cls_memMk {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ Mk) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    (stSt γ G σ Mk).cls v = some u.upper :=
  spliceFold_cls_mem (unitBlocks γ G σ Mk) (unitBlocks_pairwiseMk hM σ Mk) hu hv

/-- B1a: `stSt_cls_none` for every marked vine set. -/
theorem stSt_cls_noneMk {v : GBranch G.tree} (hv : ∀ u ∈ unitBlocks γ G σ Mk, v ∉ u.atoms) :
    (stSt γ G σ Mk).cls v = none :=
  spliceFold_cls_notMem (unitBlocks γ G σ Mk) (unitBlocks_pairwiseMk hM σ Mk) hv

end clsMk

section cls
variable {G : Garden w} (hM : G.molecule.IsMolecule) (σ : Prescription G)
include hM

theorem stSt_cls_mem {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    (stSt γ G σ).cls v = some u.upper :=
  spliceFold_cls_mem (unitBlocks γ G σ) (unitBlocks_pairwise hM σ) hu hv

theorem stSt_cls_none {v : GBranch G.tree} (hv : ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms) :
    (stSt γ G σ).cls v = none :=
  spliceFold_cls_notMem (unitBlocks γ G σ) (unitBlocks_pairwise hM σ) hv

/-- B1b (Mk-general form of `stSt_repC_mem`). -/
theorem stSt_repC_memMk {u : CLBlock G} {Mk : Set (CLVineG γ _)} (hu : u ∈ unitBlocks γ (Mk := Mk) G σ) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    repC (stSt γ (Mk := Mk) G σ).cls v = u.upper := by
  simp [repC, stSt_cls_memMk (Mk := Mk) hM σ hu hv]

theorem stSt_repC_mem {u : CLBlock G} (hu : u ∈ unitBlocks γ G σ) {v : GBranch G.tree} (hv : v ∈ u.atoms) :
    repC (stSt γ G σ).cls v = u.upper := by apply stSt_repC_memMk (Mk := ∅) <;> assumption

/-- B1b (Mk-general form of `stSt_repC_none`). -/
theorem stSt_repC_noneMk {v : GBranch G.tree} {Mk : Set (CLVineG γ _)} (hv : ∀ u ∈ unitBlocks γ (Mk := Mk) G σ, v ∉ u.atoms) :
    repC (stSt γ (Mk := Mk) G σ).cls v = v := by
  simp [repC, stSt_cls_noneMk (Mk := Mk) hM σ hv]

theorem stSt_repC_none {v : GBranch G.tree} (hv : ∀ u ∈ unitBlocks γ G σ, v ∉ u.atoms) :
    repC (stSt γ G σ).cls v = v := by apply stSt_repC_noneMk (Mk := ∅) <;> assumption

end cls

end WaveTurbulence.GammaLow.Fama
