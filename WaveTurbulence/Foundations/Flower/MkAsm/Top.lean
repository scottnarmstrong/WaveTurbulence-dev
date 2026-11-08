/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.CoreG

/-! # A5 MK-ASM: the prefix assembly. `CoreFOfComponents` and `CoreGOfComponents` from the conditional helpers.

* `coreFOfComponents_of_caps : CapsDecompF → CoreFOfComponents`
* `coreGOfComponents_of_caps : CapsDecompG → CoreGOfComponents`

The only inputs are the distinctly named conditional helpers (CAPS-ID / CAPS-COMP), and the hypothesis
`WTPrefixP (MarkedComponentBoundAtI B)` of the core statements themselves. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- Prefix bookkeeping: from a fixed-parameter implication, valid once `Pm ≥ 1`, `δ ≤ 1`, and the structure count
is absorbed (`L` large depending on `d, D, Pm`), to a statement under `WTPrefixP`. -/
theorem prefixP_of_at {Q M : ℕ → WTParams → Prop} (hM : WTPrefixP M)
    (step : ∀ (Pm : ℕ) (P : WTParams), 1 ≤ Pm → 0 < P.ν → 0 < P.δ → P.δ ≤ 1 → 1 ≤ P.L →
      (∀ N p : ℕ, N ≤ P.N (p + 1) ^ 4 →
        ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm) →
      M Pm P → Q Pm P) :
    WTPrefixP Q := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := hM d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hφs => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφ τ hτ φ hφs
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H3⟩ := H2 ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H4⟩ := H3 Pm (le_trans (le_max_left _ _) hPm)
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H5⟩ := H4 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  have hPm1 : 1 ≤ Pm := le_trans (le_max_right _ _) hPm
  obtain ⟨L₁, hL₁, hthr⟩ := exists_threshold d D Pm hPm1 (by omega)
  refine ⟨C₂, hC₂, max L₀ L₁, le_trans hL₀ (le_max_left _ _), fun L hL => ?_⟩
  have hMat := H5 L (le_trans (le_max_left _ _) hL)
  have hL1 : L₁ ≤ L := le_trans (le_max_right _ _) hL
  exact step Pm _ hPm1 hν.1 hδ.1 (hδ.2.trans (min_le_right _ _)) (by linarith)
    (fun N p hN => hthr _ rfl rfl hL1 p N hN) hMat

theorem coreFOfComponents_of_caps (hcaps : CapsDecompF) : CoreFOfComponents := by
  intro B hB0 hB hM
  exact prefixP_of_at hM fun Pm P _ hν hδ hδ1 hL hthr hMP =>
    coreF_at hB hMP (hcaps Pm P) hν hδ hδ1 hL hthr

theorem coreGOfComponents_of_caps (hcaps : CapsDecompG) : CoreGOfComponents := by
  intro B hB0 hB hM
  exact prefixP_of_at hM fun Pm P _ hν hδ hδ1 hL hthr hMP =>
    coreG_at hB hMP (hcaps Pm P) hν hδ hδ1 hL hthr

/-- The final consumer from the two conditional helpers and the marked component bound. -/
theorem flower_v3_of_marked_of_caps (hF : CapsDecompF) (hG : CapsDecompG) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : B ≤ 24000) (hM : WTPrefixP (MarkedComponentBoundAtI B)) : V2Chain.LayergardenFlowerV3Gate :=
  flower_v3_of_marked (coreFOfComponents_of_caps hF) (coreGOfComponents_of_caps hG) B hB0 hB hM

end WaveTurbulence.Flower.MkAsm
