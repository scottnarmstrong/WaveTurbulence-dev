/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.SelMerge
public import WaveTurbulence.Foundations.Flower.ProtPin.Alpha

/-! # D3 PROT-PIN (R181): `term` with one selected filter — the gate

`ProtBoundSelDisjAt` is ProtDefs' `ProtBoundSelAt` (R181 text, D6b) with the added hypothesis `v ∉ F ∨ v ∉ Fu`
(finding F-D3-Sel-1, SEL-LOG.md: D5's gates take two filter layers per branch; with `v ∈ F ∩ Fu` strictly inside a
cut piece the selected vertex carries three filter factors). Under it the multiplier is `chiDNorm⁻¹ ·` D3's flagged
two-layer multiplier (`sel_mult_merge`), and the flagged `term` route applies at `θ = 1/4` (`term_tree_final_starA`,
`term_cap_final_starA`). `protBoundSelDisjGate : WTPrefix ProtBoundSelDisjAt`, prefix as `protBoundNTGate`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin.Sel

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- `ProtBoundSelAt` with the selected vertex outside one of the two filter layers (F-D3-Sel-1). -/
def ProtBoundSelDisjAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n → X.lonePath ≠ [] → ProtAmbient p X LG →
  ∀ (v : GBranch LG.garden.tree), v.1.1.val = 0 → v.1.2 <+: X.lonePath → v.1.2 ≠ X.lonePath →
    v.1.2 ≠ X.lonePath.dropLast →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s : ℝ), (p : ℝ) < s → s < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  (v ∉ F ∨ v ∉ Fu) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr (1 / 4) (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ *
          ((Flower.MkDefs.chiDN (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s s (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (47 * P.d + 2)) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

def ProtBoundSelDisjGate : Prop := WTPrefix ProtBoundSelDisjAt

/-- **One parameter set.** -/
theorem selDisjAt_of {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    {Cr4 CL4 : ℝ} (hCr4 : 0 ≤ Cr4) (hCL4 : 0 ≤ CL4) (hperk4 : TermStarPerkUA (1 / 4) Cr4)
    (hLOE4 : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr (1 / 4) B {k} F ≤ X) →
      XNormRestr (1 / 4) (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL4 * L ^ (31 * P.d)) * X)
    (hbig4 : termK CL4 (Cr4 * FiltCoh.chiDSup ^ 2) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ)) :
    ProtBoundSelDisjAt P := by
  intro p hp n hn w LG X hsh hsz hne hamb v hv0 hvpre hvne hvterm M₂ hM₂ s hps hsp q' hq' S ω cω hpres F M hM Fu Mu
    hMu hvF ind hind H B hH b₀ c₀
  obtain ⟨F₁, ann₁, M₁, F₂, M₂', hM₁, hM₂', heq⟩ :=
    sel_mult_merge P.L v S ω F M hM Fu Mu hMu M₂ hM₂ ind hvF
  rw [show (fun κ : GNode LG.garden.tree → Mom P.d => Flower.IncTop.starWeight S ω κ *
      filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ *
      ((Flower.MkDefs.chiDN (|omegaNode LG.garden κ v| / M₂) : ℝ) : ℂ) * (ind κ : ℂ)) =
    fun κ => ((Flower.MkDefs.chiDNorm⁻¹ : ℝ) : ℂ) * (Flower.IncTop.starWeight S ω κ * filtWeight F₁ ann₁ M₁ κ *
      filtWeight F₂ (fun _ => false) M₂' κ * (ind κ : ℂ)) from funext heq]
  have hθc4 : PieceLoss P (1 / 4) (4 * P.d) := Or.inr ⟨rfl, rfl⟩
  have hc : 31 * (P.d : ℝ) + 4 * (4 * P.d) + 2 ≤ ((47 * P.d + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hpow : ENNReal.ofReal (P.L ^ (47 * P.d + 2)) = ENNReal.ofReal (P.L ^ ((47 * P.d + 2 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
  have h40 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hCx : (0 : ℝ) ≤ FiltCoh.chiDSup ^ 2 := by positivity
  rw [hpow]
  match w, LG, hsh, hamb, v, hv0, S, ω, cω, hpres, F₁, ann₁, M₁, hM₁, F₂, M₂', hM₂', ind, hind, H, B, hH, hsz with
  | 1, LG, hsh, hamb, v, hv0, S, ω, cω, hpres, F₁, ann₁, M₁, hM₁, F₂, M₂', hM₂', ind, hind, H, B, hH, hsz =>
    rw [prod_ofReal_starCost]
    exact term_tree_final_starA h40 K hθc4 hc hCr4 hCL4 hCx hperk4 hLOE4 hbig4 hp hn LG X hsh hsz
      (treeAmb_of_protAmbient hamb) hne hps hsp s q' H B hH _ (starCost S cω) (starCost_nonneg' S cω)
      (StarMultA.const_mul (starMult_treeA S ω cω hpres F₁ ann₁ M₁ hM₁ F₂ M₂' hM₂' ind hind) _
        norm_chiDNorm_inv_le) b₀ c₀
  | 2, LG, hsh, hamb, v, hv0, S, ω, cω, hpres, F₁, ann₁, M₁, hM₁, F₂, M₂', hM₂', ind, hind, H, B, hH, hsz =>
    exact term_cap_final_starA h40 K hθc4 hc hCr4 hCL4 hperk4 hLOE4 hbig4 hp hn LG X hsh hsz hamb hne hps hsp s q'
      H B hH S ω cω hpres F₁ ann₁ M₁ hM₁ F₂ M₂' hM₂' ind hind _ norm_chiDNorm_inv_le b₀ c₀
  | 0, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim
  | _ + 3, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => exact hsh.elim

/-- **`term` with one selected filter** (`v ∉ F ∨ v ∉ Fu`; unconditional otherwise). -/
theorem protBoundSelDisjGate : ProtBoundSelDisjGate := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, HI⟩ := FiltGate.filtIncoherentDecayGate d hd γ hγ
  obtain ⟨η₂, hη₂, HC⟩ := cohFlatGate d hd γ hγ
  obtain ⟨Cr4, hCr4, hperk4⟩ := exists_termStarPerkUA (θ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨CL4, hCL4, hLOE4⟩ := ProtOps.localOutputExtension d (1 / 4) (by norm_num)
  refine ⟨min (min η₁ η₂) (1 / 4), lt_min (lt_min hη₁ hη₂) (by norm_num), fun η hη φin hφ τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₁ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hη2 : η ∈ Ioc 0 η₂ := ⟨hη.1, hη.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans (min_le_right _ _)
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
  have hCx : (0 : ℝ) ≤ FiltCoh.chiDSup ^ 2 := by positivity
  set Kb := termK CL4 (Cr4 * FiltCoh.chiDSup ^ 2) d + 1 with hKb
  have hK4 := termK_nonneg hCL4 (mul_nonneg hCr4 hCx) d
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
  exact selDisjAt_of K hCr4 hCL4 hperk4 hLOE4
    (big_of_large hK4 (by linarith) hγ.2 hL1 hLb hδ.1.le hδC)

end WaveTurbulence.Flower.ProtPin.Sel
