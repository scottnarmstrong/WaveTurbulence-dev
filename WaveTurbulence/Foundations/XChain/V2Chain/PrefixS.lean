/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# V2-CHAIN: the γ-restricted parameter prefix

`WTPrefixS S Q` is the frozen `WTPrefix Q` with the extra hypothesis `γ ∈ S` on the exponent (`WTPrefix = WTPrefixS univ`);
`WTPrefixPS S Q` is the same for the `P`-indexed prefix `WTPrefixP`. The combinators of the X-chain
(`and`, `small`, `large`, `mono`, `toWTPrefixS`) are re-proved verbatim for them: the only change is that the
hypothesis `hS : γ ∈ S` is passed to every gate. `ofR`/`toR` identify `WTPrefixS (Ioo (1/2) 1) Q` with the
anchor form `WTPrefix fun P => 1 / 2 < P.γ → Q P` of the successor statements (ruling D9/D10).
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence.V2Chain

/-- The prefix `(Π)` with `γ` restricted to `S`. -/
def WTPrefixS (S : Set ℝ) (P : WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → γ ∈ S →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  P ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

/-- The prefix `(Π_P)` of `flowerest1` with `γ` restricted to `S`. -/
def WTPrefixPS (S : Set ℝ) (Q : ℕ → WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → γ ∈ S →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ P₀ : ℕ, ∀ Pm : ℕ, P₀ ≤ Pm →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  Q Pm ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

variable {S : Set ℝ}

/-- An unrestricted prefix statement is a restricted one. -/
theorem WTPrefixS.ofFull {Q : WTParams → Prop} (h : WTPrefix Q) : WTPrefixS S Q :=
  fun d hd γ hγ _ => h d hd γ hγ

theorem WTPrefixPS.ofFull {Q : ℕ → WTParams → Prop} (h : WTPrefixP Q) : WTPrefixPS S Q :=
  fun d hd γ hγ _ => h d hd γ hγ

/-- The anchor form `1/2 < γ → …` gives the restricted prefix for `S = Ioo (1/2) 1`. -/
theorem WTPrefixS.ofR {Q : WTParams → Prop} (h : WTPrefix fun P => 1 / 2 < P.γ → Q P) :
    WTPrefixS (Ioo (1 / 2 : ℝ) 1) Q := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL hS.1⟩

theorem WTPrefixS.toR {Q : WTParams → Prop} (h : WTPrefixS (Ioo (1 / 2 : ℝ) 1) Q) :
    WTPrefix fun P => 1 / 2 < P.γ → Q P := by
  intro d hd γ hγ
  by_cases hr : 1 / 2 < γ
  · obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ ⟨hr, hγ.2⟩
    refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
    obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
    refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
    obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
    refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
    obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
    exact ⟨C₂, hC₂, L₀, hL₀, fun L hL _ => H L hL⟩
  · exact ⟨1, one_pos, fun η hη φin hφ τ hτ φ hW => ⟨1, le_rfl, 1, one_pos, fun ν hν =>
      ⟨1, one_pos, fun δ hδ D hD hτD => ⟨1, le_rfl, 2, le_rfl, fun L hL hg => absurd hg hr⟩⟩⟩⟩

theorem WTPrefixPS.ofR {Q : ℕ → WTParams → Prop} (h : WTPrefixP fun Pm P => 1 / 2 < P.γ → Q Pm P) :
    WTPrefixPS (Ioo (1 / 2 : ℝ) 1) Q := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨P₀, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm hPm
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => H L hL hS.1⟩

/-! ## Combinators (the originals, with `hS` passed to every gate) -/

theorem WTPrefixS.mono {Q Q' : WTParams → Prop} (h : WTPrefixS S Q) (hQ : ∀ P, Q P → Q' P) :
    WTPrefixS S Q' := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

theorem WTPrefixPS.mono {Q Q' : ℕ → WTParams → Prop} (h : WTPrefixPS S Q) (hQ : ∀ Pm P, Q Pm P → Q' Pm P) :
    WTPrefixPS S Q' := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨P₀, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm hPm
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ _ (H L hL)⟩

theorem WTPrefixPS.toWTPrefixS {Q : ℕ → WTParams → Prop} (h : WTPrefixPS S Q) :
    WTPrefixS S fun P => ∃ Pm, Q Pm P := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  obtain ⟨δ₀, hδ₀, H⟩ := H P₀ le_rfl
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => ⟨P₀, H L hL⟩⟩

theorem WTPrefixS.and {Q₁ Q₂ : WTParams → Prop}
    (hC : ∀ (P : WTParams) (C₁ C₂ : ℝ), Q₁ P → Q₁ {P with C₁ := C₁, C₂ := C₂})
    (h₁ : WTPrefixS S Q₁) (h₂ : WTPrefixS S Q₂) : WTPrefixS S fun P => Q₁ P ∧ Q₂ P := by
  intro d hd γ hγ hS
  obtain ⟨η₁, hη₁, H₁⟩ := h₁ d hd γ hγ hS
  obtain ⟨η₂, hη₂, H₂⟩ := h₂ d hd γ hγ hS
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁a, -, ν₁, hν₁, H₁⟩ := H₁ η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφ τ hτ φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, H₂⟩ := H₂ η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφ τ hτ φ hW
  refine ⟨C₁b, hC₁b, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, H₁⟩ := H₁ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, H₂⟩ := H₂ ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, hL₁, H₁⟩ := H₁ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, hC₂b, L₂, hL₂, H₂⟩ := H₂ δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  exact ⟨C₂b, hC₂b, max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL =>
    ⟨hC _ C₁b C₂b (H₁ L ((le_max_left _ _).trans hL)), H₂ L ((le_max_right _ _).trans hL)⟩⟩

theorem WTPrefixPS.and {Q₁ Q₂ : ℕ → WTParams → Prop}
    (hC : ∀ Pm (P : WTParams) (C₁ C₂ : ℝ), Q₁ Pm P → Q₁ Pm {P with C₁ := C₁, C₂ := C₂})
    (h₁ : WTPrefixPS S Q₁) (h₂ : WTPrefixPS S Q₂) : WTPrefixPS S fun Pm P => Q₁ Pm P ∧ Q₂ Pm P := by
  intro d hd γ hγ hS
  obtain ⟨η₁, hη₁, H₁⟩ := h₁ d hd γ hγ hS
  obtain ⟨η₂, hη₂, H₂⟩ := h₂ d hd γ hγ hS
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁a, -, ν₁, hν₁, H₁⟩ := H₁ η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφ τ hτ φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, H₂⟩ := H₂ η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφ τ hτ φ hW
  refine ⟨C₁b, hC₁b, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨P₁, H₁⟩ := H₁ ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨P₂, H₂⟩ := H₂ ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨max P₁ P₂, fun Pm hPm => ?_⟩
  obtain ⟨δ₁, hδ₁, H₁⟩ := H₁ Pm ((le_max_left _ _).trans hPm)
  obtain ⟨δ₂, hδ₂, H₂⟩ := H₂ Pm ((le_max_right _ _).trans hPm)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, hL₁, H₁⟩ := H₁ δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, hC₂b, L₂, hL₂, H₂⟩ := H₂ δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  exact ⟨C₂b, hC₂b, max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL =>
    ⟨hC _ _ C₁b C₂b (H₁ L ((le_max_left _ _).trans hL)),
      H₂ L ((le_max_right _ _).trans hL)⟩⟩

theorem WTPrefixPS.small {Q : ℕ → WTParams → Prop} (h : WTPrefixPS S Q) (f : ℝ → ℝ)
    (hf : ∀ ν, 0 < ν → 0 < f ν) :
    WTPrefixPS S fun Pm P => Q Pm P ∧ 1 ≤ Pm ∧ 0 < P.ν ∧ 0 < P.δ ∧ P.δ ≤ f P.ν ∧ 2 ≤ P.L := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm ((le_max_left _ _).trans hPm)
  refine ⟨min δ₀ (f ν), lt_min hδ₀ (hf ν hν.1), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL =>
    ⟨H L hL, (le_max_right _ _).trans hPm, hν.1, hδ.1, hδ.2.trans (min_le_right _ _), hL₀.trans hL⟩⟩

theorem WTPrefixS.small {Q : WTParams → Prop} (h : WTPrefixS S Q) (f : ℝ → ℝ → ℝ)
    (hf : ∀ ν C₁, 0 < ν → 1 ≤ C₁ → 0 < f ν C₁) (g : ℕ → ℝ → ℝ) :
    WTPrefixS S fun P => Q P ∧ 3 ≤ P.d ∧ 0 < P.ν ∧ 1 ≤ P.C₁ ∧ 0 < P.δ ∧ P.δ ≤ f P.ν P.C₁ ∧ 1 ≤ P.C₂ ∧
      g P.d P.C₂ ≤ P.L ∧ 2 ≤ P.L := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨min δ₀ (f ν C₁), lt_min hδ₀ (hf ν C₁ hν.1 hC₁), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max L₀ (g d C₂), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  exact ⟨H L ((le_max_left _ _).trans hL), hd, hν.1, hC₁, hδ.1, hδ.2.trans (min_le_right _ _), hC₂,
    (le_max_right _ _).trans hL, hL₀.trans ((le_max_left _ _).trans hL)⟩

/-- `L` large after `d` and `𝔇`; and `γ ∈ (0,1)`, `0 < δ ≤ 1`. -/
theorem WTPrefixS.large {Q : WTParams → Prop} (h : WTPrefixS S Q) (g : ℕ → ℕ → ℝ) :
    WTPrefixS S fun P => Q P ∧ 3 ≤ P.d ∧ P.γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < P.δ ∧ P.δ ≤ 1 ∧ g P.d P.D ≤ P.L ∧
      2 ≤ P.L := by
  intro d hd γ hγ hS
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ hS
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max L₀ (g d D), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  exact ⟨H L ((le_max_left _ _).trans hL), hd, hγ, hδ.1, hδ.2.trans (min_le_right _ _),
    (le_max_right _ _).trans hL, hL₀.trans ((le_max_left _ _).trans hL)⟩

end WaveTurbulence.V2Chain
