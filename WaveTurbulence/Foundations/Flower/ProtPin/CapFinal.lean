/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapPin
public import WaveTurbulence.Foundations.Flower.ProtPin.TreeFinals

/-! # D3 PROT-PIN: cap couples in `X^{θ,30d,0}` for `root`, `trace`, `rootTerm`, `penTerm` ((P4) root-pinned, (P5))

`capc_root_final`, `capc_trace_final`, `capc_rootTerm_final`, `capc_pen_root_final`, `capc_pen5_final`: the per-output
bounds of CapRoot/CapPin, dispatched on the shape of the chain (one pair: `CutTermData … nil`; a suffix: `RootData`),
closed by `final_pair` / `final_term` / `final_two` with the leaf size and the star cost of the cap couple. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The paired tree of a protected cap couple and its transported data. -/
theorem capc_data {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} (hsh : ProtShape p X LG) (hamb : ProtAmbient p X LG) :
    ∃ LG1 : LayeredGarden 1, CapData X LG LG1 ∧ ProtShape p X LG1 ∧ TreeAmb p X LG1 ∧
      protSize X LG = protSize X LG1 ∧ protIncoh X LG = protIncoh X LG1 := by
  obtain ⟨LG1, Dc, h1, h2, h3⟩ := cap_pieces hsh
  exact ⟨LG1, Dc, h1, treeAmb_of_cap hamb Dc, h2, h3⟩

theorem capc_n1 {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {n : ℕ}
    (h : (RegChain.pair m Qr Qg inner rest).size = 2 * n) : 1 ≤ n := by
  rw [size_rootCut] at h
  omega

/-- **`root` for protected cap couples in `X^{θ,30d,0}`** (`ind ≡ 1`). -/
theorem capc_root_final {θ : ℝ} (hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ}
      (_hθc : PieceLoss P θ c') (_hc'0 : 0 ≤ c') (_hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (_hCL : 0 ≤ CL)
      (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : ProtAmbient p X LG) (_hne : X.lonePath ≠ [])
      {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1) (s : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind) (_hind1 : ∀ κ, ind κ = 1)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.root.box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hpair⟩ := capc_root_pair_perk hθ0
  obtain ⟨C2, hC2, hrst⟩ := capc_root_rest_perk hθ0
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' c CL hθc hc'0 hc hCL hC11 hLOE hbig p hp n hn LG X hsh hsz hamb hne t hpt htp s q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind hind1 b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1' : 0 ≤ P.C₁ := by linarith
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : X.size = 2 * n := by rw [← hsz, hsz1]; rfl
  rw [prod_ofReal_starCost, hinc1]
  cases X with
  | nil => exact absurd rfl hne
  | pair m Qr Qg inner rest =>
    have hn1 := capc_n1 hX
    by_cases hrest : rest = .nil
    · subst hrest
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 .nil m Qr Qg inner hsh1.2.1 hsh1.1
      refine final_pair K.hL K.hδ hC11 (le_max_of_le_left hC1) hCL hc'0 hc hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS
        fun k => ?_
      refine (hpair K hθc hp hn Dc C hsh1 hX hamb1 hpt htp s q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pairRb_nonneg hC1' K.hδ hL0 _ _ hleaf hCS)))
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG1 m Qr Qg inner rest hsh1.2.1 hsh1.1 hrest
      refine final_term K.hL K.hδ hC1' (le_max_of_le_left hC1) hCL hc hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS
        fun k => ?_
      refine (hrst K hθc hp hn Dc D hsh1 hX hamb1 hpt htp s q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (termRb_nonneg hC1' K.hδ hL0 _ _ hleaf hCS)))

/-- **`trace` for protected cap couples with a nonempty chain in `X^{θ,30d,0}`** (`ind ≡ 1`). -/
theorem capc_trace_final {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ}
      (_hθc : PieceLoss P θ c') (_hc'0 : 0 ≤ c') (_hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (_hCL : 0 ≤ CL)
      (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : ProtAmbient p X LG) (_hne : X.lonePath ≠ [])
      (s t : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind) (_hind1 : ∀ κ, ind κ = 1)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.trace.box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hpair⟩ := capc_trace_pair_perk hθ0 hθ1
  obtain ⟨C2, hC2, hrst⟩ := capc_trace_rest_perk hθ0 hθ1
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' c CL hθc hc'0 hc hCL hC11 hLOE hbig p hp n hn LG X hsh hsz hamb hne s t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind hind1 b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1' : 0 ≤ P.C₁ := by linarith
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : X.size = 2 * n := by rw [← hsz, hsz1]; rfl
  rw [prod_ofReal_starCost, hinc1]
  cases X with
  | nil => exact absurd rfl hne
  | pair m Qr Qg inner rest =>
    have hn1 := capc_n1 hX
    by_cases hrest : rest = .nil
    · subst hrest
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 .nil m Qr Qg inner hsh1.2.1 hsh1.1
      refine final_pair K.hL K.hδ hC11 (le_max_of_le_left hC1) hCL hc'0 hc hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS
        fun k => ?_
      refine (hpair K hθc hp hn Dc C hsh1 hX hamb1 s t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pairRb_nonneg hC1' K.hδ hL0 _ _ hleaf hCS)))
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG1 m Qr Qg inner rest hsh1.2.1 hsh1.1 hrest
      refine final_term K.hL K.hδ hC1' (le_max_of_le_left hC1) hCL hc hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS
        fun k => ?_
      refine (hrst K hθc hp hn Dc D hsh1 hX hamb1 s t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (termRb_nonneg hC1' K.hδ hL0 _ _ hleaf hCS)))

/-- **`rootTerm` ((P2), (P3)) for protected cap couples in `X^{θ,30d,0}`** (`θ` with `c' = 0`). -/
theorem capc_rootTerm_final {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : ProtAmbient p X LG)
      (_hval : ProtCfg.rootTerm.Valid X LG p) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t) (_htp : t < p + 1)
      (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind) (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.rootTerm.box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hpair⟩ := capc_rootTerm_pair_perk hθ0
  obtain ⟨C2, hC2, hrst⟩ := capc_p3_perk hθ0 hθ1
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig hbig2 p hp n hn LG X hsh hsz hamb hval s t hps hst htp q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1' : 0 ≤ P.C₁ := by linarith
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : X.size = 2 * n := by rw [← hsz, hsz1]; rfl
  have hval' : 2 ≤ X.lonePath.length := hval
  rw [prod_ofReal_starCost, hinc1]
  cases X with
  | nil => simp [RegChain.lonePath] at hval'
  | pair m Qr Qg inner rest =>
    by_cases hrest : rest = .nil
    · subst hrest
      have hn1 := capc_n1 hX
      obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 .nil m Qr Qg inner hsh1.2.1 hsh1.1
      have hc' : 31 * (P.d : ℝ) + 4 * 0 + 2 ≤ c := by linarith
      refine final_pair K.hL K.hδ hC11 (le_max_of_le_left hC1) hCL le_rfl hc' hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS
        fun k => ?_
      refine (hpair K hθc hp hn Dc C hsh1 hX hamb1 hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pairRb_nonneg hC1' K.hδ hL0 _ _ hleaf hCS)))
    · obtain ⟨LGZ, LGi, LGs, LGr, LGg, D⟩ := RootData.exists_of_wf LG1 m Qr Qg inner rest hsh1.2.1 hsh1.1 hrest
      have hn2 : 2 ≤ n := by
        obtain ⟨ns, _, _, _, hns, -, -, -, h⟩ := root_sizes hX
        have := pen_size_two rest D.rest_lonePath_ne
        omega
      refine final_two K.hL K.hδ hC1' (le_max_of_le_left hC1) hCL (a := 7 * 0) (by norm_num) hc hLOE hbig2 _ b₀ c₀
        _ hn2 hleaf hCS fun k => ?_
      refine (hrst K hθc hp hn Dc D hsh1 hX hamb1 hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind
        k).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (twoRb_nonneg hC1' K.hδ hL0 _ _ _ hleaf hCS)))

/-- **(P4) with the root pinned for protected cap couples in `X^{θ,30d,0}`.** -/
theorem capc_pen_root_final {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c CL : ℝ}
      (_hθc : PieceLoss P θ c') (_hc'0 : 0 ≤ c') (_hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) (_hCL : 0 ≤ CL)
      (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) {m : MiniTreeCode}
      {Qr Qg : RegCpl} (_hsh : ProtShape p (appendChain .nil (cpair m Qr Qg .nil)) LG)
      (_hsz : protSize (appendChain .nil (cpair m Qr Qg .nil)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain .nil (cpair m Qr Qg .nil)) LG) {s t : ℝ} (_hps : (p : ℝ) < s)
      (_hst : s < t) (_htp : t < p + 1) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain .nil (cpair m Qr Qg .nil)) ind) (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (appendChain .nil (cpair m Qr Qg .nil)) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hperk⟩ := capc_pen_root_perk hθ0
  refine ⟨C1, hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' c CL hθc hc'0 hc hCL hC11 hLOE hbig p hp n hn LG m Qr Qg hsh hsz hamb s t hps hst htp q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : (cpair m Qr Qg .nil).size = 2 * n := by rw [← hsz, hsz1]; rfl
  have hn1 := capc_n1 hX
  rw [prod_ofReal_starCost, hinc1]
  obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 .nil m Qr Qg .nil hsh1.2.1 hsh1.1
  exact final_pair K.hL K.hδ hC11 hC1 hCL hc'0 hc hLOE hbig _ b₀ c₀ _ hn1 hleaf hCS fun k =>
    hperk K hθc hp hn Dc C hsh1 hX hamb1 hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k

/-- **(P5) for protected cap couples in `X^{θ,30d,0}`** (`θ` with `c' = 0`). -/
theorem capc_pen5_final {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) {Xp : RegChain}
      {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} (_hin : inner.lonePath ≠ [])
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : protSize (appendChain Xp (cpair m Qr Qg inner)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain Xp (cpair m Qr Qg inner)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg inner)) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hperk⟩ := capc_pen5_perk hθ0 hθ1
  refine ⟨C1, hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hLOE hbig2 p hp n hn LG Xp m Qr Qg inner hin hsh hsz hamb s hps hsp t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hC1' : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n := by rw [← hsz, hsz1]; rfl
  have hn2 : 2 ≤ n := by
    obtain ⟨np, ni, nr, ng, -, hni, -, -, h⟩ := cut_sizes hX
    have := pen_size_two inner hin
    omega
  rw [prod_ofReal_starCost, hinc1]
  obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 Xp m Qr Qg inner hsh1.2.1 hsh1.1
  exact final_two K.hL K.hδ hC1' hC1 hCL (a := 7 * 0) (by norm_num) hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf hCS fun k =>
    hperk K hθc hp hn Dc C hin hsh1 hX hamb1 hps hsp t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k

end WaveTurbulence.Flower.ProtPin
