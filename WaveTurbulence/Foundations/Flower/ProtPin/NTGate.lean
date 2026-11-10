/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.NoneGate
public import WaveTurbulence.Foundations.Flower.ProtPin.Alpha

/-! # D3 PROT-PIN: the configurations `none` and `term` with star weights, filters and the dagger

`protBoundNTGate : ProtBoundNTGate`: `ProtBoundAt` at `cfg ∈ {none, term}` (both weights `(η, 31d+6)` and
`(1/4, 47d+2)`, every star weight presented with `30d` moments, both filter layers with scales `≥ L`, the dagger),
unconditional. `none`: `none_tree`/`none_cap`; `term`: `term_tree_final_star`/`term_cap_final_star` with
`starMult_tree`/`starMult_cap`. The prefix is that of milestone α (`protBoundAlphaGate`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **`none` and `term` at one parameter set.** -/
theorem ntAt_of {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {Crη CLη Cr4 CL4 : ℝ} (hCrη : 0 ≤ Crη) (hCLη : 0 ≤ CLη) (hCr4 : 0 ≤ Cr4) (hCL4 : 0 ≤ CL4)
    (hperkη : TermStarPerkU P.η Crη) (hperk4 : TermStarPerkU (1 / 4) Cr4)
    (hLOEη : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr P.η B {k} F ≤ X) →
      XNormRestr P.η (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CLη * L ^ (31 * P.d)) * X)
    (hLOE4 : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr (1 / 4) B {k} F ≤ X) →
      XNormRestr (1 / 4) (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL4 * L ^ (31 * P.d)) * X)
    (hbigη : termK CLη Crη P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hbig4 : termK CL4 Cr4 P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ)) :
    ProtBoundNTAt P := by
  intro p hp n hn w LG X hsh hsz cfg hval hamb hcfg θ c hθc s t hps hst htp q' hq' S ω cω hpres F M hM Fu Mu hMu
    ind hind hind1 H B hH b₀ c₀
  have hθc' : (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2) := by
    rcases hθc with h | ⟨h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  have hsp : s < p + 1 := hst.trans htp
  rcases hcfg with rfl | rfl
  · exact noneAt_of K p hp n hn w LG X hsh hsz .none hval hamb rfl θ c hθc s t hps hst htp q' hq' S ω cω hpres
      F M hM Fu Mu hMu ind hind hind1 H B hH b₀ c₀
  · have hne : X.lonePath ≠ [] := hval
    rcases hθc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hc : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ 31 * P.d + 6 := by linarith
      have hθc0 : PieceLoss P P.η 0 := Or.inl ⟨rfl, rfl⟩
      match w, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz with
      | 1, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz =>
        rw [prod_ofReal_starCost]
        exact term_tree_final_star K.hη0 K hθc0 hc hCrη hCLη hperkη hLOEη hbigη hp hn LG X hsh hsz
          (treeAmb_of_protAmbient hamb) hne hps hsp t q' H B hH _ _ (starCost_nonneg' S cω)
          (starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind) b₀ c₀
      | 2, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz =>
        exact term_cap_final_star K.hη0 K hθc0 hc hCrη hCLη hperkη hLOEη hbigη hp hn LG X hsh hsz hamb hne hps hsp
          t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
      | 0, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
      | _ + 3, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
    · have hc : 31 * (P.d : ℝ) + 4 * (4 * P.d) + 2 ≤ 47 * P.d + 2 := by linarith
      have hθc4 : PieceLoss P (1 / 4) (4 * P.d) := Or.inr ⟨rfl, rfl⟩
      have h40 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      match w, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz with
      | 1, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz =>
        rw [prod_ofReal_starCost]
        exact term_tree_final_star h40 K hθc4 hc hCr4 hCL4 hperk4 hLOE4 hbig4 hp hn LG X hsh hsz
          (treeAmb_of_protAmbient hamb) hne hps hsp t q' H B hH _ _ (starCost_nonneg' S cω)
          (starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind) b₀ c₀
      | 2, LG, hsh, hamb, S, ω, cω, hpres, F, M, hM, Fu, Mu, hMu, ind, hind, H, B, hH, hsz =>
        exact term_cap_final_star h40 K hθc4 hc hCr4 hCL4 hperk4 hLOE4 hbig4 hp hn LG X hsh hsz hamb hne hps hsp
          t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
      | 0, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
      | _ + 3, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim

end WaveTurbulence.Flower.ProtPin
