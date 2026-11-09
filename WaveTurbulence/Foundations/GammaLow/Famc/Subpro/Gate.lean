/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.SubproFinalR83
public import WaveTurbulence.Foundations.GammaLow.Fama.Normalized
/-! # subpro′: the S4 obligation for the normalized `𝒱_γ` Stage 1 piece (packet L5c, item E)

TARGET Prop `subpro` (2)–(6) (L2040–L2053) over `𝒱_γ`, `γ ≤ 1/2`, for L5a's normalized construction
(`Fama.VineA.NormalizedSplice.stage1PieceOf`): main's `VineA.NormalizedSplice.Subpro.subproObligationA`
(Stage1/Geometry/SubproFinal2R83.lean), at the exact type of L5a's named input `Fama.NormalizedSubproInput`
(`Fama/Normalized.lean`), which L5a's `normalizedStage1Piece_sound` consumes.

The proof is main's: the construction facts (L5a's `construction_facts`) give the plainness of the spliced garden,
and `subproSupportA` (ported, `Famc/Subpro/SubproFinalR83.lean`) gives the decorated conditions for every decoration in
the support of the epsilon and gap factors. Its conclusion `SubproSupportA γ` has the same fields as L6's
`Src.SubproSupport γ` (whose `OutsideAtoms` is the atom-set containment by definition). No named inputs beyond
the three L5a construction inputs, which are hypotheses of `NormalizedSubproInput`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.Subpro
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.RedSplice WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

/-- **subpro′ (item E): `Fama.NormalizedSubproInput` holds.** For every `P` with `P.γ ≤ 1/2` and every prime
skeleton, the S4 obligation holds for the normalized `𝒱_γ` Stage 1 piece. -/
theorem normalizedSubpro : Fama.NormalizedSubproInput := by
  intro _ _ _ P _ R S D hS LG hd σ hP hI hbal hn p hN hlayer hL base roots
  obtain ⟨hB, -, -⟩ := Fama.VineA.NormalizedSplice.construction_facts (γ := P.γ) S hP hI hbal hn σ
    (RegRed.coreLayer LG D hS hd) p (P.N (p + 1) ^ 4) hN hlayer
  intro z hε hZ
  have h := VineA.NormalizedSplice.Subpro.subproSupportA (γ := P.γ) σ _ rfl hB.plain hL P.γ P.η base roots z hε hZ
  exact ⟨h.selectedSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩

end WaveTurbulence.GammaLow.Famc.Subpro
