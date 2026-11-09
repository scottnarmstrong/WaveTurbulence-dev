/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.LowCounting
/-! # The gate over the fixed low family `γL` (packet L6, items H/I)

`FinalCountLAt P` is `FinalCountGammaAt P` with the counting choices over the fixed family parameter `γL = 1/2` (the
carrier of the ported stage-2 run, PLAN-L6 §3c). For `P.γ ≤ 1/2` it implies `FinalCountGammaAt P`: recast the
choices (`Src.CountingChoices.recast`), which keeps the hinges, the ladder scales and `numCriticalSG`, and transports
`CountingGeometry` and the admissibility. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-- `FinalCountGammaAt` over the fixed low carrier `Src.CountingChoices γL`. -/
abbrev FinalCountLAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : Src.CountingChoices Src.γL G P.d),
    D.hinges = C.subpro.hinges → Src.CountingGeometry G C →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → Src.splicedCountingAdmissible G D C P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

/-- The gate body at `γ ≤ 1/2` from its `γL` form. -/
theorem finalCountGammaAt_of_L {P : WTParams} (hγ : P.γ ≤ 1 / 2) (h : FinalCountLAt P) : FinalCountGammaAt P := by
  intro p hp R hR hRm G hpl hirr hbal hn hnm D C hD hg base roots Adm hA
  have := h p hp R hR hRm G hpl hirr hbal hn hnm D (C.recast hγ Src.γL_le) hD
    (Src.countingGeometry_recast hγ Src.γL_le hg) base roots Adm
    (fun κ hκ => Src.splicedCountingAdmissible_recast hγ Src.γL_le (hA κ hκ))
  rwa [Src.CountingChoices.recast_ladderScale, Src.CountingChoices.numCriticalSG_recast] at this

/-- **`FinalCountGateLow` from the `γL` form** (the target of the ported run). -/
theorem finalCountGateLow_of_L (h : WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountLAt P) : FinalCountGateLow := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL hγ' => finalCountGammaAt_of_L hγ' (H L hL hγ')⟩

end WaveTurbulence.GammaLow.FinalCount
