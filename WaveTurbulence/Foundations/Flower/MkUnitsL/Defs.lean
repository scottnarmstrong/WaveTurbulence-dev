/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Defs
public import WaveTurbulence.Foundations.Flower.V5W2L.Defs

/-! # MK-UNITS-L (B3-2): the marked producer with per-unit top filters (statements)

On a clean point a capped stem can pass through the upper joint `u₁` of a spliced unit (F-B3s-4, ruling R179): σ's stem
filter and/or a selection shell `χ₀(|Ω_{u₁}|/s)` then sit INSIDE the unit kernel, possibly several layers. B3-2 re-runs
B3's unit chain (`Flower/MkUnits`) with a filter list `SU j : List ℝ` at the upper joint of every unit `j`, the unit
kernels being V5W-2L's `unitRecenteredFWL p g (SU j)` (top weight `topFilterWeightL (SU j)`), the weighted vine class
bound V5W-2L's `V5FrontierClassBoundAtL` (an isolated hypothesis).

* `runClassAt a p kind Mk`: the run class of the piece of `a` at the marked set `Mk` (its members `y` carry the units
  `y.2 j`).
* `UnitTopFilters L p a Mk SU base roots E`: on every member of the run class, the extra weight `E` (a function of the
  layered garden's decoration) is the product over the units of `topFilterWeightL (SU j)` at the unit's upper joint,
  read on the collapsed skeleton decoration of the member's reconstruction.
* `VineCaseRepresentsFWMkL`, `MarkedUnitsRepresentsFWL`: B3's exports with the class sum of
  `valueSelW … (fun κ => fwWeight p g base LG κ * E LG κ)` and the size `cψ^{16N} · topFilterMass^{∑ⱼ |SU j|} · s`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.MkUnitsL
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
  WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
  WaveTurbulence.RedSplice WaveTurbulence.VineC WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkUnits WaveTurbulence.VineEstS4

/-- The run class of the piece of `a` at the marked set `Mk` (members `y` carry the units `y.2 j`). -/
noncomputable abbrev runClassAt {w : ℕ} (a : PrescribedPrimeGarden w) (p : ℕ) (kind : Bool)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) :=
  classU (unitsSplit (alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)) p kind
    (startAt a Mk)
    (unitsRegion (alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)
      (VineB.unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma Mk))

/-- **Per-unit top filters presenting an extra weight** (F-B3s-4): the filter lengths are positive, and on every
member `y` of the run class of `a` at `Mk` the extra weight `E` on the member's reconstruction is the product over the
units `j` of `topFilterWeightL (SU j)` at the unit's upper joint, read on the collapsed skeleton decoration. -/
def UnitTopFilters {d R : ℕ} (L : ℝ) (p : ℕ) (a : PrescribedPrimeGarden (2 * R))
    (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma Mk).length → List ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ))
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden d roots 0 → ℂ) : Prop :=
  (∀ j, ∀ s ∈ SU j, 0 < s) ∧
  ∀ y ∈ runClassAt a p (objKind (2 * R)) Mk,
    ∀ κ : GenDecoration (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)).garden d roots 0,
      E _ κ = ∏ j, VineSpaceK.nodeWeight (V5W2L.topFilterWeightL (SU j)) L base (y.2 j).blk.a
        (collapseGenDecoration y.1.data y.1.plain κ).1

/-- **O3′ at a marking with per-unit top filters (B3-2)**: `VineCaseRepresentsFWMk` with the extra weight `E` presented
by the unit top filters `SU`, and the size factor `topFilterMass ^ (∑ j, (SU j).length)`. -/
def VineCaseRepresentsFWMkL (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
  ∀ (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop), TwistClosedAdm p A Adm →
  ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)), MarkingOK mkF mkC →
    (∀ a : PrescribedPrimeGarden (2 * R), a.layered ∈ A → Adm (startAt a (mkAt mkF a))) →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π)) ≠ [] →
  ∀ (SU : Fin (unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π))).length → List ℝ)
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ),
    UnitTopFilters P.L p (repPt π) (mkAt mkF (repPt π)) SU base roots E →
    Stage1Piece.RepresentsInt (P := P) ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))) N tt base roots
      (cψ ^ (16 * N) * V5W.topFilterMass ^ (∑ j, (SU j).length) * s)
      (∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fun κ => fwWeight p g base LG κ * E LG κ))

/-- **The B3-2 main export**: both cases (vine and vine-free; in the vine-free case there is no unit and `E = 1` on
the class) in `RepresentsIntMK` form, with per-unit top filters. -/
def MarkedUnitsRepresentsFWL (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Mk.Stage1CarriesW P p N LG) →
  ∀ (Adm : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop), TwistClosedAdm p A Adm →
  ∀ (mkF mkC : Stage1Mk.MarkFn (2 * R)), MarkingOK mkF mkC →
    (∀ a : PrescribedPrimeGarden (2 * R), a.layered ∈ A → Adm (startAt a (mkAt mkF a))) →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    (∀ j x, (g j x).im = 0) →
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
  ∀ (SU : Fin (unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkAt mkF (repPt π))).length → List ℝ)
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ),
    UnitTopFilters P.L p (repPt π) (mkAt mkF (repPt π)) SU base roots E →
  ∀ (surv : SurvivorData ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))).Gsb) (nProt : ℕ) (cP : ℝ), 0 ≤ cP →
    (pieceMK ((repPt π).normalizedPiece P.d (mkAt mkF (repPt π))) surv nProt).RepresentsIntMK N cP tt base roots
      (cψ ^ (16 * N) * V5W.topFilterMass ^ (∑ j, (SU j).length) * s)
      (∑ LG ∈ membersP (clsPMk mkC π), valueSelW U.toLF tt base roots LG
        (selPMk p (objKind (2 * R)) A P base roots mkF π LG) (fun κ => fwWeight p g base LG κ * E LG κ))

end WaveTurbulence.Flower.MkUnitsL
