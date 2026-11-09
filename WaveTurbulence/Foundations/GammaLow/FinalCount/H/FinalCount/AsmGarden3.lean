/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGarden3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGarden2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGarden3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level, 3): base independence of the gap notions** (`HasGapKind`, `SubproOblG`, `SGat`, `DegenSGT`,
`SourceLadderGaps`).  The counting hypotheses are stated at the base of `FinalCountAt`; the chain runs at base `0`.  Gaps are base independent
(`gapAt_base_indep`), hence so is every notion defined through `gapAt`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem vineLike_isGap_base_indep {M : Molecule V D} {S : Finset V} {a b : V} (C : Src.VineLikeObject Src.γL M S a b) (L : ℝ) (w w' : Mom d)
    (κ : D → (Fin d → ℤ)) (r : Mom d) : C.IsGap L w κ r ↔ C.IsGap L w' κ r := by
  cases C with
  | vc h => exact isBlockGap_base_indep M L w w' κ S a r
  | hyper R => exact isBlockGap_base_indep _ L w w' _ S a r

theorem object_hasGapKind_base_indep {M : Molecule V D} (O : Src.Object Src.γL M) (L γ η : ℝ) (w w' : Mom d)
    (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) : O.HasGapKind L γ η w κ k ↔ O.HasGapKind L γ η w' κ k := by
  unfold Src.Object.HasGapKind
  exact exists_congr fun r => and_congr_left' (vineLike_isGap_base_indep O.shape L w w' κ r)

theorem subproOblG_base_indep {M : Molecule V D} (C : CollData M) (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) :
    SubproOblG C L γ η w κ ↔ SubproOblG C L γ η w' κ := by
  have hhost : ∀ P : Src.Object Src.γL M, C.Host L γ η w κ P ↔ C.Host L γ η w' κ P := by
    intro P
    unfold CollData.Host
    simp only [object_hasGapKind_base_indep _ L γ η w w' κ]
  have hsg : ∀ P : Src.Object Src.γL M, P.HasGapKind L γ η w κ .SG ↔ P.HasGapKind L γ η w' κ .SG :=
    fun P => object_hasGapKind_base_indep P L γ η w w' κ _
  constructor
  · intro h
    refine ⟨fun P hP hO hD => (hhost P).1 (h.contained P ((hsg P).2 hP) hO hD), fun v hv => ?_, h.hingeJoint, fun P hP hO hD => ?_⟩
    · exact (hasChosenPair_congr' fun x y => by simp only [gapAt_base_indep L w w' κ]).1 (h.hingeSG v hv)
    · obtain ⟨v, hv, hvP, hr⟩ := h.crossing P ((hsg P).2 hP) hO hD
      exact ⟨v, hv, hvP, hr⟩
  · intro h
    refine ⟨fun P hP hO hD => (hhost P).2 (h.contained P ((hsg P).1 hP) hO hD), fun v hv => ?_, h.hingeJoint, fun P hP hO hD => ?_⟩
    · exact (hasChosenPair_congr' fun x y => by simp only [gapAt_base_indep L w w' κ]).1 (h.hingeSG v hv)
    · obtain ⟨v, hv, hvP, hr⟩ := h.crossing P ((hsg P).1 hP) hO hD
      exact ⟨v, hv, hvP, hr⟩

end WaveTurbulence.GammaLow.FinalCount.H
