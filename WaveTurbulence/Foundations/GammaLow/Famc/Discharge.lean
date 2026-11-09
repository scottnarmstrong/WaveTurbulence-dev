/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.TVine.Struct.Final
public import WaveTurbulence.Foundations.GammaLow.Famc.Glue
public import WaveTurbulence.Foundations.GammaLow.Famc.Layervine.Improved
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.VineCode
/-! # Discharge of L5c's L3 named inputs (L3's `TVine.Struct.Final`, proved unconditionally)

L3 proved its T-vine structure statements (`TVine.Struct.Final`: `subObjects_holds`, `pieceShape_holds`,
`layervine_holds`). Every L3 named input of L5c except `LaddersInput` (N3 Theorem 6 (iv), still open at L3) is
discharged here, and the exports that carried them are restated unconditionally. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.Induct WaveTurbulence.LGSpine

theorem subObjectsInput_holds : SubObjectsInput := TVine.Struct.subObjects_holds
theorem pieceShapeInput_holds : PieceShapeInput := TVine.Struct.pieceShape_holds
theorem layervineInput_holds : LayervineInput := TVine.Struct.layervine_holds
theorem tvineStructInputs_holds : ClassCount.TVineStructInputs :=
  ⟨TVine.Struct.layervine_holds, TVine.Struct.pieceShape_holds⟩

/-- **The counting cover over `𝒱_γ`, unconditional** (`fineSplicedChoicesGamma` with `SubObjectsInput` discharged). -/
theorem fineSplicedChoicesGamma_uncond (P : WTParams) (hfourier : LadderFourierAt P)
    (hcount : FinalCount.FinalCountGammaAt P) (hs : CoverSmall P) : FineSplicedChoicesGammaAt P :=
  fineSplicedChoicesGamma subObjectsInput_holds P hfourier hcount hs

/-- **layervine′, first bound**, from L3's ladder statement only. -/
theorem layervineTVineFirst_of_ladders (hLad : LaddersInput) : LayervineTVineFirst :=
  layervineTVineFirst hLad pieceShapeInput_holds

/-- **layervine′, improved bound**, from L3's ladder statement only. -/
theorem layervineTVineImproved_of_ladders (hLad : LaddersInput) : LayervineTVineImproved :=
  layervineTVineImproved hLad pieceShapeInput_holds layervineInput_holds

/-- **finalsbest2 for a `𝒱_γ` Stage 1 piece, without `SubObjectsInput`.** -/
theorem stage1Piece_fine_gamma_uncond {P : WTParams} {R : ℕ} (hfourier : LadderFourierAt P)
    (hcount : FinalCount.FinalCountGammaAt P) (hs : CoverSmall P) (π : Fama.Stage1PieceG P R) {p : ℕ}
    (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (hπ : π.Sound p base roots) (tt : Fin (2 * R) → ℝ)
    (ctr : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ)
    (hD : SplicedAmplitudeBounds π.Gsb (π.data tt ctr edge hinge freq)) :
    ‖splicedKernel π.Gsb (π.data tt ctr edge hinge freq) P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ π.Gsb.order *
        P.L ^ (-P.η ^ 6 * (π.Gsb.molecule.rho + (π.data tt ctr edge hinge freq).hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) :=
  stage1Piece_fine_gamma subObjectsInput_holds hfourier hcount hs π hp hR hRmax hπ tt ctr edge hinge freq hD

end WaveTurbulence.GammaLow.Famc
