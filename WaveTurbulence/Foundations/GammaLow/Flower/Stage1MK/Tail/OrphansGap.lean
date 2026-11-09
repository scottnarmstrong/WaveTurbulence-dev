/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L8-I-ORPHANS port of main `WaveTurbulence.Foundations.Vine.A.{VineGapProfile, VineNormalizedGapIndicator,
-- VinePieceProfile, VinePlainA4}` (marked parts; sha256 in Tail/Orphans-COPIED-SHA256SUMS), over 𝒱_γ on L5a's ports.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGapProfile
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePieceProfile
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Fama.Discharge
public import WaveTurbulence.Foundations.Vine.A.VinePlainA4
/-! # Item I orphans: the marked gap profile over `𝒱_γ`

Main's `VineA.GapValueSelDartsMk` (B1b-3: B2c's dart-label gap identity at every garden, prescription and marking — a
hypothesis in main, carried as such), `NormalizedSplice.splicedGapIndicatorSelOfAt_of_selDarts`,
and `BatchIso.gapProfileMk` (over L8's `vineA_gapProfileMkLow`, = L5a's `Fama.VineA.gapProfileMk` by `rfl`; L8's
`familyPieceProfileMkLow`/`profileMkLow` are in `Stage1MK.P7`), over L5a's ports
(`Fama.VineA.gapProfileMk`, `operation_gapProfileMk`, `isV0Fam_operationMk`, `Stage1Mk.markTransported_split`,
`NormalizedSplice.{GapValueSelDartsAt, SplicedGapIndicatorSelOfAt, gapValue_eq_indicatorMk, stage1PieceOf}`). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Stage1 WaveTurbulence.VineA
  WaveTurbulence.LGSpine

variable {γF : ℝ} [Fact (γF ≤ 1 / 2)]

/-- B1b-3: B2c's dart-label gap identity at every garden of width `w`, prescription and marking (main
`VineA.GapValueSelDartsMk`; a hypothesis in main). -/
def GapValueSelDartsMkLow (w : ℕ) : Prop :=
  ∀ (H : Garden w) (τ : Prescription H) (M : Set (Fama.CLVineG γF H)),
    Fama.VineA.NormalizedSplice.GapValueSelDartsAt γF H τ M

/-- B1b-3: the dart-label form implies B2c's exact statement (main
`NormalizedSplice.splicedGapIndicatorSelOfAt_of_selDarts`). -/
theorem splicedGapIndicatorSelOfAt_of_selDartsLow {w : ℕ} {G : Garden w} {σ : Prescription G}
    {Mk : Set (Fama.CLVineG γF G)} (h : Fama.VineA.NormalizedSplice.GapValueSelDartsAt γF G σ Mk) :
    Fama.VineA.NormalizedSplice.SplicedGapIndicatorSelOfAt γF G σ Mk := by
  intro d L γ' η base c z hκ hc0 zsb hlab D hD
  rw [← Fama.VineA.NormalizedSplice.gapValue_eq_indicatorMk σ D hD]
  exact h L γ' η base c (bondIndex G z) hκ hc0 zsb hlab

/-- L8's `vineA_gapProfileMkLow` (P2) is L5a's `Fama.VineA.gapProfileMk` (same construction). -/
theorem vineA_gapProfileMkLow_eq_fama {w : ℕ} (G : Garden w) (σ : Prescription G) (Mk : Set (Fama.CLVineG γF G)) :
    vineA_gapProfileMkLow G σ Mk = Fama.VineA.gapProfileMk γF G σ Mk := rfl

/-- B1b-3: the gap profile at markings carried by an actual batch (main `BatchIso.gapProfileMk`, stated with L8's
`vineA_gapProfileMkLow`). -/
theorem batchIso_gapProfileMkLow {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (Fama.CLVineG γF A.skeleton)}
    {Mk' : Set (Fama.CLVineG γF B.skeleton)} (hT : Fama.Stage1Mk.MarkTransported γF F Mk Mk')
    (hA : Fama.VineA.IsV0Fam γF A.family σ Mk) (hg : GapValueSelDartsMkLow (γF := γF) w) :
    vineA_gapProfileMkLow B.skeleton (transportPrescription F σ) Mk' =
      vineA_gapProfileMkLow A.skeleton σ Mk := by
  rw [vineA_gapProfileMkLow_eq_fama, vineA_gapProfileMkLow_eq_fama]
  induction h with
  | nil =>
    obtain rfl := Fama.Stage1Mk.markTransported_refl_eq hT
    exact congrArg (fun τ => Fama.VineA.gapProfileMk γF _ τ Mk) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hT hA
  | @apply L A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Fama.Stage1Mk.markTransported_split (operationMolIso op) F hT
    have hb := ih _ h2 (Fama.VineA.isV0Fam_operationMk hA op h1)
    rw [transportPrescription_trans] at hb
    exact hb.trans (Fama.VineA.operation_gapProfileMk hA op h1 (hg _ _ _) (hg _ _ _))

end WaveTurbulence.GammaLow.Flower
