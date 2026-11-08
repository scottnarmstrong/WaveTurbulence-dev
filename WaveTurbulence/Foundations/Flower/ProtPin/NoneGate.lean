/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.None
public import WaveTurbulence.Foundations.Flower.ProtPin.CohGate

/-! # D3 PROT-PIN: the `none` configuration with star weights and filters

`protBoundNoneGate : ProtBoundNoneGate`: `ProtBoundAt` at `cfg = none`, any star weights and filter layers (both
weights, the dagger is `1`). Incoherent objects: FILT-GATE (star- and filter-weighted); coherent objects: the flat
coherent gate (`CohFlatAt`, star- and filter-weighted). Prefix: `η₀ = min(η₀^{inc}, η₀^{coh}, 1/4)`,
`C₁ = max`, `ν₀ = min`, `δ₀ = min`, `C₂ = 1`, `L₀ = max(L₀^{inc}, L₀^{coh}, 2)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-- **`none` at one parameter set.** -/
theorem noneAt_of {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) :
    ProtBoundNoneAt P := by
  intro p hp n hn w LG X hsh hsz cfg _ hamb hcfg θ c hθc s t _ _ _ q' hq' S ω cω hpres F M hM Fu Mu hMu
    ind _ hind1 H B hH b₀ c₀
  subst hcfg
  have hθc' : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2) := by
    rcases hθc with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hi1 : ∀ κ, ind κ = 1 := hind1 (Or.inl rfl)
  match w, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, H, B, hH, ind, hi1, hsz with
  | 1, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, H, B, hH, ind, hi1, hsz =>
    exact none_tree K hp hn LG X hsh hsz hamb hθc' s t hq' S ω cω hpres F M hM Fu Mu hMu ind hi1 H B hH b₀ c₀
  | 2, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, H, B, hH, ind, hi1, hsz =>
    exact none_cap K hp hn LG X hsh hsz hamb hθc' s t hq' S ω cω hpres F M hM Fu Mu hMu ind hi1 H B hH b₀ c₀
  | 0, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
  | _ + 3, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim

/-- **The `none` configuration of `ProtBoundAt`** (star weights and filters; unconditional). -/
theorem protBoundNoneGate : ProtBoundNoneGate := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  refine ⟨min (min η₁ η₂) (1 / 4), lt_min (lt_min hη₁ hη₂) (by norm_num), fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hη2 : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁a, hC₁a, ν₁, hν₁, HI1⟩ := HI η hη1 φin hφ τs hτs φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, HC1⟩ := HC η hη2 φin hφ τs hτs φ hW
  refine ⟨max C₁a C₁b, le_max_of_le_left hC₁a, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, HI2⟩ := HI1 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, HC2⟩ := HC1 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, -, HI3⟩ := HI2 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  obtain ⟨C₂b, -, L₂, -, HC3⟩ := HC2 δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD hτD
  refine ⟨1, le_rfl, max (max L₁ L₂) 2, le_max_right _ _, fun L hL => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : (2 : ℝ) ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  exact noneAt_of (⟨HI3 L hL₁, HC3 L hL₂, by linarith, by linarith, le_max_left _ _, le_max_right _ _, hδ.1.le,
    hL1, hη.1.le, hη4, hd⟩ : AlphaConsts ⟨d, γ, η, φin, τs, φ, max C₁a C₁b, ν, δ, D, 1, L⟩ C₁a C₂a C₁b C₂b)

end WaveTurbulence.Flower.ProtPin
