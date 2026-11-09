/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Statement
public import WaveTurbulence.Foundations.GammaLow.Flower.NamedInputs
public import WaveTurbulence.Foundations.FlowerTop.FinalAssembly
public import WaveTurbulence.Foundations.FlowerTop.MomentPrefix

/-! # FLOWER-LOW (packet L8), item B (1/6): the flower case split and the final assembly, `0 < γ ≤ 1/2`

Main's `FlowerTop.{CaseAssembly, FinalAssembly}` γ-carrying declarations copied by source (sha256 in
`COPIED-SHA256SUMS`), with `1 / 2 < P.γ` replaced by `P.γ ≤ 1 / 2` and each copied name suffixed `Low`
(`layergardenFlower_v3_of_inputs` ↦ `flower_low_of_inputs`). The γ hypothesis is only threaded. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.FlowerTop
open LGSpine Set

/-- The flower half of frozen v3, restricted to the cutoff indices selected by `case`. -/
def FlowerCaseAtLow (case : Option ℕ → Option ℕ → Prop) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
      case cut1 cut2 →
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
      FlowerBoundAt P R p N Pm kind pat dagger cut1 cut2 ζ t s n n'

end

section
open WaveTurbulence.FlowerTop
open LGSpine Set

/-- The four cases together are the frozen flower half. -/
theorem flowerCase_topLow {Pm : ℕ} {P : WTParams}
    (h0 : FlowerCaseAtLow CasePlain Pm P) (h1 : FlowerCaseAtLow CaseCut1 Pm P)
    (h2 : FlowerCaseAtLow CaseCut2Pos Pm P) (h3 : FlowerCaseAtLow CaseCut2Zero Pm P) :
    FlowerCaseAtLow (fun _ _ => True) Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 _ hcut
  rcases cut2 with _ | j
  · rcases cut1 with _ | j₁
    · exact h0 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger none none ⟨rfl, rfl⟩ hcut
    · exact h1 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger (some j₁) none ⟨rfl, rfl⟩ hcut
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact h3 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 (some 0) rfl hcut
    · exact h2 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 (some j) ⟨j, rfl, hj⟩ hcut

end

section
open WaveTurbulence.FlowerTop
open LGSpine Set

theorem flowerCase_largeConstantMonotoneLow (case : Option ℕ → Option ℕ → Prop) (Pm : ℕ) :
    LargeConstantMonotone (FlowerCaseAtLow case Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  unfold FlowerBoundAt at H ⊢
  rw [hF, flowerSumP_largeConstants]
  simpa only [N_largeConstants, WTParams.Lambda] using H

end

section
open WaveTurbulence.FlowerTop
open LGSpine Set

/-- The couple half of frozen v3, in the frozen body's shape. -/
def CoupleHalfAtLow (_Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
      (dt : Bool), (kind = .tr → dt = true) →
      ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
        jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)

end

section
open WaveTurbulence.FlowerTop
open LGSpine Set

theorem coupleHalf_largeConstantMonotoneLow (Pm : ℕ) : LargeConstantMonotone (CoupleHalfAtLow Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht k N hN kind dt hkdt
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht k N hN kind dt hkdt
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  simpa only [coupleSum, N_largeConstants, hF, WTParams.Lambda] using H

end

section
open WaveTurbulence.FlowerTop
open LGSpine Set

/-- **The frozen `layergardenFlower_v3` body**, from one prefix input per clause. Nothing is bundled:
`hPlain`, `hCut1`, `hCut2`, `hCut2Zero`, `hCouple`. -/
theorem flower_low_of_inputs
    (hPlain : WTPrefixP (FlowerCaseAtLow CasePlain))
    (hCut1 : WTPrefixP (FlowerCaseAtLow CaseCut1))
    (hCut2 : WTPrefixP (FlowerCaseAtLow CaseCut2Pos))
    (hCut2Zero : WTPrefixP (FlowerCaseAtLow CaseCut2Zero))
    (hCouple : WTPrefixP CoupleHalfAtLow) : LayergardenFlowerLowGate := by
  have h01 := prefixP_and hPlain hCut1 (flowerCase_largeConstantMonotoneLow _) (flowerCase_largeConstantMonotoneLow _)
  have h012 := prefixP_and h01 hCut2
    (fun Pm => (flowerCase_largeConstantMonotoneLow _ Pm).and (flowerCase_largeConstantMonotoneLow _ Pm))
    (flowerCase_largeConstantMonotoneLow _)
  have h0123 := prefixP_and h012 hCut2Zero
    (fun Pm => ((flowerCase_largeConstantMonotoneLow _ Pm).and (flowerCase_largeConstantMonotoneLow _ Pm)).and
      (flowerCase_largeConstantMonotoneLow _ Pm))
    (flowerCase_largeConstantMonotoneLow _)
  have hall := prefixP_and h0123 hCouple
    (fun Pm => (((flowerCase_largeConstantMonotoneLow _ Pm).and (flowerCase_largeConstantMonotoneLow _ Pm)).and
      (flowerCase_largeConstantMonotoneLow _ Pm)).and (flowerCase_largeConstantMonotoneLow _ Pm))
    coupleHalf_largeConstantMonotoneLow
  refine prefixP_map hall ?_
  rintro Pm P ⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, c⟩ hγ p hp R hR
  have hF := flowerCase_topLow a0 a1 a2 a3 hγ p hp R hR
  refine ⟨?_, c hγ p hp R hR⟩
  intro t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hcut
  exact hF t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 trivial hcut

end

end WaveTurbulence.GammaLow.Flower
