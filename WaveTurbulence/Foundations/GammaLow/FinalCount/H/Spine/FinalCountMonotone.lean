/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FinalCountMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.FinalCountMonotone`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Large-constant monotonicity of `FinalCountAt` (the counting input `finalcount1`, TARGET L2114-L2116).
`countA` decreases in `C_1` because its circuit rank is nonnegative (`circuitRank_nonneg`), so the bound
at one `C_1` implies the bound at every larger `C_1`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open WaveTurbulence Finset
open scoped ENNReal

theorem finalCountAt_largeConstantMonotone : LargeConstantMonotone FinalCountAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots
    Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

end WaveTurbulence.GammaLow.FinalCount.H
