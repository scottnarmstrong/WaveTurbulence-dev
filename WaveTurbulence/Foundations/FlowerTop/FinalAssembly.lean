/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.CaseAssembly
public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes

/-! Final assembly of the frozen `layergardenFlower_v3` body from its five clause inputs (main world). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine Set

theorem prefixP_map {A B : ℕ → WTParams → Prop} (hA : WTPrefixP A) (hmap : ∀ Pm P, A Pm P → B Pm P) :
    WTPrefixP B := by
  intro d hd γ hγ
  obtain ⟨η₀, h0, H⟩ := hA d hd γ hγ
  refine ⟨η₀, h0, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H3⟩ := H2 ν hν
  refine ⟨P₀, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ, H4⟩ := H3 Pm hPm
  refine ⟨δ₀, hδ, fun δ hδ' D hD ht => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H5⟩ := H4 δ hδ' D hD ht
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hmap _ _ (H5 L hL)⟩

theorem prefixP_and {A B : ℕ → WTParams → Prop} (hA : WTPrefixP A) (hB : WTPrefixP B)
    (hmA : ∀ Pm, LargeConstantMonotone (A Pm)) (hmB : ∀ Pm, LargeConstantMonotone (B Pm)) :
    WTPrefixP (fun Pm P => A Pm P ∧ B Pm P) := by
  intro d hd γ hγ
  obtain ⟨ηA, hηA, hA⟩ := hA d hd γ hγ
  obtain ⟨ηB, hηB, hB⟩ := hB d hd γ hγ
  refine ⟨min ηA ηB, lt_min hηA hηB, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨CA, hCA, νA, hνA, hA⟩ := hA η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  obtain ⟨CB, hCB, νB, hνB, hB⟩ := hB η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨max CA CB, hCA.trans (le_max_left _ _), min νA νB, lt_min hνA hνB, ?_⟩
  intro ν hν
  obtain ⟨PA, hA⟩ := hA ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨PB, hB⟩ := hB ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨max PA PB, ?_⟩
  intro Pm hPm
  obtain ⟨δA, hδA, hA⟩ := hA Pm ((le_max_left _ _).trans hPm)
  obtain ⟨δB, hδB, hB⟩ := hB Pm ((le_max_right _ _).trans hPm)
  refine ⟨min δA δB, lt_min hδA hδB, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂A, hC₂A, LA, hLA, hA⟩ := hA δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨C₂B, hC₂B, LB, hLB, hB⟩ := hB δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD htime
  refine ⟨max C₂A C₂B, hC₂A.trans (le_max_left _ _), max LA LB, hLA.trans (le_max_left _ _), ?_⟩
  intro L hL
  constructor
  · exact hmA Pm _ _ _ hCA hC₂A hδ.1 (hLA.trans ((le_max_left _ _).trans hL)) (le_max_left _ _)
      (le_max_left _ _) (hA L ((le_max_left _ _).trans hL))
  · exact hmB Pm _ _ _ hCB hC₂B hδ.1 (hLB.trans ((le_max_right _ _).trans hL)) (le_max_right _ _)
      (le_max_right _ _) (hB L ((le_max_right _ _).trans hL))

/-- The couple half of frozen v3, in the frozen body's shape. -/
def CoupleHalfAt (_Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
      (dt : Bool), (kind = .tr → dt = true) →
      ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
        jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)

theorem coupleHalf_largeConstantMonotone (Pm : ℕ) : LargeConstantMonotone (CoupleHalfAt Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht k N hN kind dt hkdt
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht k N hN kind dt hkdt
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  simpa only [coupleSum, N_largeConstants, hF, WTParams.Lambda] using H

/-- **The frozen `layergardenFlower_v3` body**, from one prefix input per clause. Nothing is bundled:
`hPlain`, `hCut1`, `hCut2`, `hCut2Zero`, `hCouple`. -/
theorem layergardenFlower_v3_of_inputs
    (hPlain : WTPrefixP (FlowerCaseAt CasePlain))
    (hCut1 : WTPrefixP (FlowerCaseAt CaseCut1))
    (hCut2 : WTPrefixP (FlowerCaseAt CaseCut2Pos))
    (hCut2Zero : WTPrefixP (FlowerCaseAt CaseCut2Zero))
    (hCouple : WTPrefixP CoupleHalfAt) : V2Chain.LayergardenFlowerV3Gate := by
  have h01 := prefixP_and hPlain hCut1 (flowerCase_largeConstantMonotone _) (flowerCase_largeConstantMonotone _)
  have h012 := prefixP_and h01 hCut2
    (fun Pm => (flowerCase_largeConstantMonotone _ Pm).and (flowerCase_largeConstantMonotone _ Pm))
    (flowerCase_largeConstantMonotone _)
  have h0123 := prefixP_and h012 hCut2Zero
    (fun Pm => ((flowerCase_largeConstantMonotone _ Pm).and (flowerCase_largeConstantMonotone _ Pm)).and
      (flowerCase_largeConstantMonotone _ Pm))
    (flowerCase_largeConstantMonotone _)
  have hall := prefixP_and h0123 hCouple
    (fun Pm => (((flowerCase_largeConstantMonotone _ Pm).and (flowerCase_largeConstantMonotone _ Pm)).and
      (flowerCase_largeConstantMonotone _ Pm)).and (flowerCase_largeConstantMonotone _ Pm))
    coupleHalf_largeConstantMonotone
  refine prefixP_map hall ?_
  rintro Pm P ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, c⟩ hγ p hp R hR
  have hF := flowerCase_top a0 a1 a2 a3 hγ p hp R hR
  refine ⟨?_, c hγ p hp R hR⟩
  intro t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hcut
  exact hF t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 trivial hcut

end WaveTurbulence.FlowerTop
