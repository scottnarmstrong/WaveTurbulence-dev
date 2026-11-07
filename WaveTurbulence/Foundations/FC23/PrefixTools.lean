/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Frozen.Defs.WTPrefixP
/-! The moment order precedes delta in the exact frozen WTPrefixP prefix. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FC23
open Filter

theorem prefixP_small_moment {Q : ℕ → WTParams → Prop} (h : WTPrefixP Q)
    (f : ℕ → ℕ → ℝ → ℝ) (hf : ∀ d m ν, 0 < ν → 0 < f d m ν) :
    WTPrefixP fun Pm P => Q Pm P ∧ 1 ≤ Pm ∧ 3 ≤ P.d ∧ 0 < P.ν ∧ 0 < P.δ ∧
      P.δ ≤ f P.d Pm P.ν ∧ 2 ≤ P.L := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨P₀, H⟩ := H ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H Pm ((le_max_left _ _).trans hPm)
  refine ⟨min δ₀ (f d Pm ν), lt_min hδ₀ (hf d Pm ν hν.1), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL =>
    ⟨H L hL, (le_max_right _ _).trans hPm, hd, hν.1, hδ.1,
      hδ.2.trans (min_le_right _ _), hL₀.trans hL⟩⟩

theorem prefixP_late {Q S : ℕ → WTParams → Prop} (hQ : WTPrefixP Q)
    (hS : ∀ (Pm : ℕ), 1 ≤ Pm → ∀ (P : WTParams),
      (∀ L : ℝ, P.L ≤ L → Q Pm {P with L := L}) →
      ∀ᶠ L : ℝ in atTop, S Pm {P with L := L}) : WTPrefixP S := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨P₀, hQ⟩ := hQ ν hν
  refine ⟨max P₀ 1, fun Pm hPm => ?_⟩
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ Pm ((le_max_left _ _).trans hPm)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ hδ D hD htime
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (hS Pm ((le_max_right _ _).trans hPm) ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L₀⟩ (fun L hL => hQ L hL))
  exact ⟨C₂, hC₂, max L₀ L₁, hL₀.trans (le_max_left _ _),
    fun L hL => hL₁ L ((le_max_right _ _).trans hL)⟩
end WaveTurbulence.FC23
