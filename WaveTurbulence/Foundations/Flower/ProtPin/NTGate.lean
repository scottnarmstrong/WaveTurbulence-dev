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

/-- **The configurations `none` and `term` of `ProtBoundAt`** (stars, filters, dagger; unconditional). -/
theorem protBoundNTGate : ProtBoundNTGate := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  obtain ⟨Cr4, hCr4, hperk4⟩ := exists_termStarPerkU (θ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨CL4, hCL4, hLOE4⟩ := ProtOps.localOutputExtension d (1 / 4) (by norm_num)
  refine ⟨min (min η₁ η₂) (1 / 4), lt_min (lt_min hη₁ hη₂) (by norm_num), fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hη2 : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
  obtain ⟨Crη, hCrη, hperkη⟩ := exists_termStarPerkU (θ := η) hη.1.le hη4
  obtain ⟨CLη, hCLη, hLOEη⟩ := ProtOps.localOutputExtension d η hη.1.le
  obtain ⟨C₁a, hC₁a, ν₁, hν₁, HI1⟩ := HI η hη1 φin hφ τs hτs φ hW
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, HC1⟩ := HC η hη2 φin hφ τs hτs φ hW
  set C₁ := max C₁a C₁b with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_of_le_left hC₁a
  refine ⟨C₁, hC₁1, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨δ₁, hδ₁, HI2⟩ := HI1 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨δ₂, hδ₂, HC2⟩ := HC1 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  have hC₁p : 0 < C₁ ^ 2 := by positivity
  refine ⟨min (min δ₁ δ₂) (1 / C₁ ^ 2), lt_min (lt_min hδ₁ hδ₂) (by positivity), fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂a, -, L₁, -, HI3⟩ := HI2 δ ⟨hδ.1, hδ.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩ D hD hτD
  obtain ⟨C₂b, -, L₂, -, HC3⟩ := HC2 δ ⟨hδ.1, hδ.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩ D hD hτD
  have hδC : δ * C₁ ^ 2 ≤ 1 := by
    have h := hδ.2.trans (min_le_right _ _)
    rw [le_div_iff₀ hC₁p] at h
    exact h
  set Kb := termK CLη Crη d + termK CL4 Cr4 d + 1 with hKb
  have hKη := termK_nonneg hCLη hCrη d
  have hK4 := termK_nonneg hCL4 hCr4 d
  refine ⟨1, le_rfl, max (max L₁ L₂) (max 2 (Kb ^ (1 / (2 - 2 * γ)))), le_max_of_le_right (le_max_left _ _),
    fun L hL => ?_⟩
  have hL₁ : L₁ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL₂ : L₂ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLb : Kb ^ (1 / (2 - 2 * γ)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith
  have K : AlphaConsts ⟨d, γ, η, φin, τs, φ, C₁, ν, δ, D, 1, L⟩ C₁a C₂a C₁b C₂b :=
    ⟨HI3 L hL₁, HC3 L hL₂, by linarith, by linarith, le_max_left _ _, le_max_right _ _, hδ.1.le, hL1, hη.1.le, hη4,
      hd⟩
  exact ntAt_of K hCrη hCLη hCr4 hCL4 hperkη hperk4 (hLOEη) (hLOE4)
    (big_of_large hKη (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)
    (big_of_large hK4 (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)

end WaveTurbulence.Flower.ProtPin
