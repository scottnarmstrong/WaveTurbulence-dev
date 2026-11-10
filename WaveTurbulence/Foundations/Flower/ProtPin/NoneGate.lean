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

end WaveTurbulence.Flower.ProtPin
