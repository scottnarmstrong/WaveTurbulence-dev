/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.Spine.FinalCountMonotone
/-! # The final-count gate for `0 < γ ≤ 1/2` (packet L6, FINALCOUNT-LOW)

TARGET `finalcount1` (L2114–L2116) with the vine family `𝒱_γ` (ruling D11). `FinalCountGammaAt` is main's
`LGSpine.FinalCountAt` verbatim (binders, order, conclusion), with main's source carrier
`LGSpine.SourceVine.{CountingChoices, CountingGeometry}` and `LGSpine.splicedCountingAdmissible` replaced by their
`𝒱_γ` copies `Src.{CountingChoices P.γ, CountingGeometry, splicedCountingAdmissible}`. The conclusion is main's:
M2 §8 (research-m2/NOTES.md) gives (together3) at `γ ≤ 1/2` with the same exponents.

`FinalCountGateLow` is the low half, in the form glued by `wtPrefix_of_halves`
(`WTPrefix fun P => P.γ ≤ 1 / 2 → Q P`). Its consumer (L7) uses it where main uses `FinalCountGateHalf`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-- TARGET finalcount1 (L2114–L2116) over `𝒱_γ`: `LGSpine.FinalCountAt` with the `𝒱_γ` source carrier `Src`. -/
abbrev FinalCountGammaAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : Src.CountingChoices P.γ G P.d),
    D.hinges = C.subpro.hinges → Src.CountingGeometry G C →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → Src.splicedCountingAdmissible G D C P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- **The final-count gate for `0 < γ ≤ 1/2`** (the low half of row 6 of the spine, with `𝒱_γ`). -/
abbrev FinalCountGateLow : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountGammaAt P

/-- Large-constant monotonicity of `FinalCountGammaAt` (as main's `finalCountAt_largeConstantMonotone`). -/
theorem finalCountGammaAt_largeConstantMonotone : LargeConstantMonotone FinalCountGammaAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots
    Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

/-- Large-constant monotonicity of the low-half body (as main's `finalCountHalf_largeConstantMonotone`). -/
theorem finalCountLow_largeConstantMonotone :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → FinalCountGammaAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    finalCountGammaAt_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

end WaveTurbulence.GammaLow.FinalCount
