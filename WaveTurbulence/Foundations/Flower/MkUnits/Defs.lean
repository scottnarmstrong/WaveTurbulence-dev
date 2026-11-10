/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Crude
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD12
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW

/-! # MK-UNITS (B3): the statements of the marked producer for the unmarked units

Stage 1′ (o75 §2.5 with U-clock, enlarged marking, B0 §2) splices the **runs** of the marked groups and the units of
the unmarked groups: `unitBlocks G σ Mk` (main, B1a/B2a).  Each run is a unit of main's on-chain U-clock chain, and the
world's weighted pieces (O3′ = `Stage1WVine`, O4′ = `Stage1WNoVine`) are reused over runs.  With the enlarged marking no
lower slot of a unit contains a protected vertex, so no protected-slot input enters here (B3s adds the protected
non-lower slots and the `G_sb` pins).

* `MarkingOK mkF mkC`: the marking data consumed (fine marking `mkF`, coarse marking `mkC ⊆ mkF`, fine transport,
  member markings).  B4 supplies them from B2b (`markInvariantBatchV_markI`, `markInvariantBatchV_markI0`).
* `VineCaseRepresentsFWMk`, `NoVineRepresentsFWMk`: O3′/O4′ for the fine′ pieces `PcA R p kind A mkF` of the marked
  producer, with the coarse′ classes `clsPMk mkC`, the twist closure `TwistClosedAdm` and the truncation-free
  carrier `Stage1CarriesW` (R156).
* `pieceMK`: a producer piece as a world `Stage1PieceMK` with no pins, no filters and indicator `1`;
  `MarkedUnitsRepresentsFW`: both cases in `RepresentsIntMK` form (the B3 export consumed by B3s/B4).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.MkUnits
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
  WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
  WaveTurbulence.RedSplice WaveTurbulence.VineC WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.MkDefs

/-! ## The marking data -/

/-! ## The R173 instance at a piece (ruling R177, F-B4-3) -/

/-- **The marking of the piece of a prescribed point** (R177, F-B4-3): the fine marking restricted to `𝒱₀(σ)`, so
that every marked vine of the piece lies in an SG group (R173).  A `MarkFn` cannot see `σ`; the restriction is made
at the piece. -/
def mkAt {w : ℕ} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Set (Stage1.CLVine a.prime.skeleton) :=
  mkF a.prime ∩ vinesV0 a.prime.skeleton a.totalSigma

/-- The start state of the run assembly of `a` at the marked set `Mk` (`sourceStart a mk` is `startAt a (mk a.prime)`
definitionally). -/
noncomputable abbrev startAt {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :=
  unitsStart (alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
    (VineB.unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma Mk) a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)

/-- A marking function taking the value `Mk` at `a.prime` (used internally to run main's `MarkFn`-level run
assembly at a marked set of the representative). -/
def fixMark {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) : Stage1Mk.MarkFn w :=
  fun _ => {c | ∃ c₀ ∈ Mk, HEq c₀ c}

theorem fixMark_self {w : ℕ} (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    fixMark a Mk a.prime = Mk := by
  ext c
  constructor
  · rintro ⟨c₀, h₀, he⟩
    rw [← eq_of_heq he]
    exact h₀
  · intro hc
    exact ⟨c, hc, HEq.rfl⟩

/-- Restricting the fine marking to `𝒱₀(σ)` does not change the unmarked `𝒱₀`. -/
theorem vinesV0_mkAt {w : ℕ} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    vinesV0 a.prime.skeleton a.totalSigma (mkAt mkF a) = vinesV0 a.prime.skeleton a.totalSigma (mkF a.prime) := by
  ext c
  rw [mem_vinesV0 (Mk := mkAt mkF a), mem_vinesV0 (Mk := mkF a.prime)]
  constructor
  · rintro ⟨h0, hn⟩
    exact ⟨h0, fun hm => hn ⟨hm, h0⟩⟩
  · rintro ⟨h0, hn⟩
    exact ⟨h0, fun hm => hn hm.1⟩

/-- Markings with the same unmarked `𝒱₀` have the same fine′ outputs. -/
theorem outputs_congr_of_vinesV0 {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w) {mk mk' : Stage1Mk.MarkFn w}
    (h : vinesV0 a.prime.skeleton a.totalSigma (mk a.prime) = vinesV0 a.prime.skeleton a.totalSigma (mk' a.prime)) :
    a.outputs (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mk' := by
  unfold PrescribedPrimeGarden.outputs PrescribedPrimeGarden.state PrimeData.fineState
  exact PrimeData.state_allCoreOutputs_congr _ h _ _

/-- The internal units marking of the piece of `a` has the fine′ outputs of the fine marking. -/
theorem outputs_fixMark_mkAt {w p : ℕ} {kind : Bool} (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    a.outputs (p := p) (kind := kind) (fixMark a (mkAt mkF a)) = a.outputs (p := p) (kind := kind) mkF :=
  outputs_congr_of_vinesV0 a (by rw [fixMark_self]; exact vinesV0_mkAt mkF a)

/-! ## O3′ and O4′ at a marking -/

/-! ## The `RepresentsIntMK` form -/

end WaveTurbulence.Flower.MkUnits
