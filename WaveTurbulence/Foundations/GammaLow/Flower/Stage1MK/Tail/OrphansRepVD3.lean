/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L8-I-ORPHANS port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVD3.hZ_commonMk`
-- (sha256 in Tail/Orphans-COPIED-SHA256SUMS), over 𝒱_γ on L5a-G's ports (Fama.P.Stage1.Represents.RepVD3, Vine.Align.*).
module
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.OrphansGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Export
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.MemberShape
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.Align.Units
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD3
/-! # Item I orphans: the common gap identity at a marking (main `Represents.hZ_commonMk`) over `𝒱_γ`

The gap indicator of the transported group prescription equals the marked piece profile's gap value on the common
shape's restricted decoration, given B2c's dart-label gap identity at every marking (`GapValueSelDartsMkLow`, a
hypothesis in main). Proof as main's: `commonShape_resDecMk`, `batchIso_gapProfileMkLow`, `gapValue_stShapeMk`,
`splicedGapIndicatorSelOfAt_of_selDartsLow`, main's family-free `gapProfile_value_cast`. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.VineA
  WaveTurbulence.VineB WaveTurbulence.RegRed WaveTurbulence.GammaLow.FinalCount WaveTurbulence.LGSpine WaveTurbulence.VineC

variable {γF : ℝ} [Fact (γF ≤ 1 / 2)]

open scoped Classical in
/-- **Main's `Represents.hZ_commonMk` over `𝒱_γ`.** -/
theorem hZ_commonMkLow {p : ℕ} {kind : Bool} {R : ℕ} (a : Fama.VineA.PrescribedPrimeGarden γF (2 * R))
    (mk : Fama.Stage1Mk.MarkFn γF (2 * R))
    {Y : FamilyReconstruction (2 * R) (Famb.VineC.UnitsIndexΓ (Fama.sourceAssemblyMk γF a mk))}
    {vs : ∀ j, UnitAt Y.skeleton Y.family ((Famb.VineC.unitsSplitΓ (Fama.sourceAssemblyMk γF a mk)).Q j)}
    {L : List (Famb.VineC.UnitsIndexΓ (Fama.sourceAssemblyMk γF a mk))}
    (hr : ReachU p kind (Famb.VineC.unitsSplitΓ (Fama.sourceAssemblyMk γF a mk)).Q L (Fama.sourceStart γF a mk)
      (Fama.sourceUnitsMk γF a mk) Y vs)
    (hn : L.Nodup) {Mk' : Set (Fama.CLVineG γF Y.skeleton)}
    (hT : Fama.Stage1Mk.MarkTransported γF (batchMolIso hr.batch) (mk a.prime) Mk')
    (hg : GapValueSelDartsMkLow (γF := γF) (2 * R))
    {d : ℕ} {Lc : ℝ} (hL : Lc ≠ 0) (γ' η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (κ : GenDecoration Y.skeleton d roots 0) :
    (if Fama.VineA.NormalizedSplice.selOf γF
        (Fama.VineA.transportGroupPrescription γF (batchMolIso hr.batch) a.sigma) Lc γ' η base κ.1
      then (1 : ℝ) else 0) =
    (Fama.VineA.PrescribedPrimeGarden.profileMkLow a mk).gap.value d Lc γ' η hL base roots
      ((Fama.commonShapeMk (Mole.garden_isMolecule a.prime.skeleton)
          (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a) a.prime.data a.prime.prime.1
          (Fama.sourceLayer γF a) (Fama.sourceLayer_isLayering a) hr hn hT).resDec Y.plain
        (Fama.member_disjMk (Mole.garden_isMolecule a.prime.skeleton)
          (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a) a.prime.data a.prime.prime.1
          (Fama.sourceLayer γF a) (Fama.sourceLayer_isLayering a) hr hn) κ) := by
  rw [Fama.Represents.commonShape_resDecMk]
  have hQP := batchIso_gapProfileMkLow (batchMolIso_spec hr.batch)
    (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a) hT
    (Fama.unitsFamily_isV0FamMk (Mole.garden_isMolecule a.prime.skeleton)
      (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a)) hg
  have h1 := Fama.Represents.gapValue_stShapeMk (Mole.garden_isMolecule Y.skeleton) Y.plain
    (transportPrescription (batchMolIso hr.batch) (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a)) (Mk := Mk')
    (splicedGapIndicatorSelOfAt_of_selDartsLow (hg _ _ Mk')) hL γ' η base roots κ
  have h2 := WaveTurbulence.Represents.gapProfile_value_cast hQP d Lc γ' η hL base roots
    ((Fama.stShape γF (Mole.garden_isMolecule Y.skeleton)
        (transportPrescription (batchMolIso hr.batch) (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a)) Mk').resDec
      Y.plain (Fama.unitBlkMk_disj (Mole.garden_isMolecule Y.skeleton)
        (transportPrescription (batchMolIso hr.batch) (Fama.VineA.PrescribedPrimeGarden.totalSigma γF a)) Mk') κ)
  exact (congrArg (fun σ => if Fama.VineA.NormalizedSplice.selOf γF σ Lc γ' η base κ.1 then (1 : ℝ) else 0)
    (Fama.Represents.ofPrescription_transport_total a (batchMolIso hr.batch)).symm).trans (h1.symm.trans h2)

end WaveTurbulence.GammaLow.Flower
