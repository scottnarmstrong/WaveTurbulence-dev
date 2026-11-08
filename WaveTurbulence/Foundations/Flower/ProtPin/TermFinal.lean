/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermAlpha
public import WaveTurbulence.Foundations.RegStruct.TreeDecodingAuxiliary

/-! # D3 PROT-PIN: `term` for protected paired trees and cap couples, in the frozen norm -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- With the terminal node pinned, the port time is irrelevant (the only lone parent is pinned). -/
theorem kernelProt_port_term {d : ℕ} (L γ δ : ℝ) {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s₁ s₂ s t T : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M up s₁ (ProtCfg.term.fix X s t T) k (fun _ => 0) 0 =
      kernelProt L γ δ LG H M up s₂ (ProtCfg.term.fix X s t T) k (fun _ => 0) 0 := by
  have hset : ∀ s' : ℝ, kDomainFix LG up (ProtCfg.term.fix X s t T) ∩
      {τ | ∀ b, LG.garden.IsLoneParent b → ProtCfg.term.fix X s t T b = none → s' < τ b} =
      kDomainFix LG up (ProtCfg.term.fix X s t T) := by
    intro s'
    refine Set.inter_eq_left.mpr fun τ _ b hb hfix => absurd hfix ?_
    obtain ⟨ℓ, hℓ, h1, i, hi⟩ := hb
    have hl : ℓ.1.2 = X.lonePath := (Reg.decodesTree_lone_iff hX ℓ).1 hℓ
    have hbp : b.1.2 = X.lonePath.dropLast := by rw [← hl, hi, List.dropLast_concat]
    unfold ProtCfg.fix ProtCfg.pins
    rw [if_pos (Nat.lt_one_iff.mp b.1.1.isLt), hbp]
    simp
  unfold kernelProt
  rw [hset s₁, hset s₂]

/-- **`term`, protected paired tree, one output, explicit constant.** -/
theorem term_tree_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      (LG : LayeredGarden 1) (X : RegChain) (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n)
      (_hamb : TreeAmb p X LG) (_hne : X.lonePath ≠ []) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (t q' : ℝ)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (M : (GNode LG.garden.tree → Mom P.d) → ℂ) (_hM : GoodMult LG X M) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG B)) := by
  obtain ⟨C, hC, hperk⟩ := term_perk hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG X hsh hsz hamb hne s hps hsp t q' H B hH M hM k
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, LGp, LGi, LGr, LGg, D⟩ := cutTerm_pieces hsh hne
  obtain ⟨Mc, Mp, Mi, Mr, Mg, hMf, hMp, hMi, hMr, hMg, hMc⟩ := hM D rfl
  refine (hperk K hθc hp hn D hsh hsz hamb hps hsp t q' H B hH M Mc Mp Mi Mr Mg hMf hMp hMi hMr hMg hMc k).trans
    (le_of_eq ?_)
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hR : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
      (P.C₁ ^ 3 * rb P (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
        leafSizeProduct LG B := by
    have := rb_nonneg hC1 K.hδ hL0 (n - 1) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
    have := Real.rpow_nonneg hL0 (4 * c')
    have : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    have := latC_nonneg P.d
    positivity
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]

/-- The constant of `term` at weight `θ` (with the LOE constant `CL`). -/
def termK (CL Cr : ℝ) (d : ℕ) : ℝ := CL * Cr * latC d ^ 2 / 4

theorem termK_nonneg {CL Cr : ℝ} (hCL : 0 ≤ CL) (hCr : 0 ≤ Cr) (d : ℕ) : 0 ≤ termK CL Cr d := by
  unfold termK; positivity

/-- **`term` in `X^{θ,30d,0}` for a protected paired tree**, from the per-output bound and `LocalOutputExtension`. -/
theorem term_tree_final {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c Cr CL : ℝ} (hθc : PieceLoss P θ c') (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL)
    (hperk : ∀ {p : ℕ}, p < P.D → ∀ {n : ℕ}, n ≤ P.N (p + 1) ^ 4 → ∀ (LG : LayeredGarden 1) (X : RegChain),
      ProtShape p X LG → protSize X LG = 2 * n → TreeAmb p X LG → X.lonePath ≠ [] → ∀ {s : ℝ}, (p : ℝ) < s →
      s < p + 1 →
      ∀ (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      ∀ (M : (GNode LG.garden.tree → Mom P.d) → ℂ), GoodMult LG X M → ∀ k : Mom P.d,
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG B)))
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : TreeAmb p X LG) (hne : X.lonePath ≠ []) {s : ℝ}
    (hps : (p : ℝ) < s)
    (hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (M : (GNode LG.garden.tree → Mom P.d) → ℂ) (hM : GoodMult LG X M)
    (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k
        (fun _ => 0) 0) ≤
      ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hn1 : 1 ≤ n := by
    have h2 := hsz
    change X.size = 2 * n at h2
    obtain ⟨Xp, m, Qr, Qg, inner, rfl, -⟩ := cutTerm_pieces hsh hne
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := cut_sizes h2
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hr := rb_nonneg hC1 K.hδ hL0 (n - 1) (protIncoh X LG)
  refine (hLOE P.L K.hL (timeBoxGt p q') b₀ c₀ _ _ fun k _ =>
    (XNorm00Restr_single_le_rn θ _ _ k).trans (hperk hp hn LG X hsh hsz hamb hne hps hsp t q' H B hH M hM k)).trans ?_
  have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0 _
  have hCδr : 0 ≤ P.C₁ * P.δ * rb P (n - 1) (protIncoh X LG) := mul_nonneg (mul_nonneg hC1 K.hδ) hr
  rw [← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)), regBound_eq_rb, rb_succ P hn1,
    ← ENNReal.ofReal_mul hLc, ← ENNReal.ofReal_mul (mul_nonneg hLc hCδr)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := term_final_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := 1)
    (leaf := leafSizeProduct LG B) (r := rb P (n - 1) (protIncoh X LG)) (c := c) (c' := c') K.hL K.hδ hC1 hCr hCL
    zero_le_one hleaf hr rfl hbig hc
  simpa only [one_mul] using this

/-- **`term` for a protected cap couple**: its paired tree times the input of the cap pair. -/
theorem term_cap_final {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c Cr CL : ℝ} (hθc : PieceLoss P θ c') (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL)
    (hperk : ∀ {p : ℕ}, p < P.D → ∀ {n : ℕ}, n ≤ P.N (p + 1) ^ 4 → ∀ (LG : LayeredGarden 1) (X : RegChain),
      ProtShape p X LG → protSize X LG = 2 * n → TreeAmb p X LG → X.lonePath ≠ [] → ∀ {s : ℝ}, (p : ℝ) < s →
      s < p + 1 →
      ∀ (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      ∀ (M : (GNode LG.garden.tree → Mom P.d) → ℂ), GoodMult LG X M → ∀ k : Mom P.d,
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H M (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG B)))
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) (hne : X.lonePath ≠ [])
    {s : ℝ} (hps : (p : ℝ) < s)
    (hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (M Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hind : TermChildIndicator X ind) (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight ∅ ω κ * filtWeight ∅ (fun _ => false) M κ *
          filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨LG1, Dc, hsh1, hsz1, hinc1⟩ := cap_pieces hsh
  set M' := fun κ : GNode LG.garden.tree → Mom P.d => Flower.IncTop.starWeight ∅ ω κ *
    filtWeight ∅ (fun _ => false) M κ * filtWeight ∅ (fun _ => false) Mu κ * (ind κ : ℂ) with hM'
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  -- leaves
  set B1 : (Fin 1 × TTree.Path) → NNReal := fun z => B ((0 : Fin 2), z.2) with hB1
  have hℓ0 : Dc.ℓ0 ∈ inputLeaves LG.garden := by rw [Dc.inputLeaves_cap]; exact Finset.mem_insert_self _ _
  have hH1 : LeafwiseControlled LG1 (capH H) B1 := fun ℓ hℓ => by
    have hm : Dc.ιL ℓ ∈ inputLeaves LG.garden := by
      rw [Dc.inputLeaves_cap]; exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hℓ)
    exact hH _ hm
  have hleafeq : leafSizeProduct LG B = (B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 B1 := by
    unfold leafSizeProduct
    rw [Dc.inputLeaves_cap, Finset.prod_insert Dc.lone_not_input, Finset.prod_map]
    rfl
  have hβ : 0 ≤ (B Dc.ℓ0.1 : ℝ) := NNReal.coe_nonneg _
  have hleaf1 : 0 ≤ leafSizeProduct LG1 B1 := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hn1 : 1 ≤ n := by
    have h2 : X.size = 2 * n := by rw [← hsz, hsz1]; rfl
    obtain ⟨Xp, m, Qr, Qg, inner, rfl, -⟩ := cutTerm_pieces hsh1 hne
    obtain ⟨_, _, _, _, -, -, -, -, h⟩ := cut_sizes h2
    omega
  have hr := rb_nonneg hC1 K.hδ hL0 (n - 1) (protIncoh X LG)
  -- the kernel: the cap input times the paired tree
  have hker : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d),
      kernelProt P.L P.γ P.δ LG H M' (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0 =
        (H ((0 : Fin 2), X.lonePath) k : ℂ) * kernelProt P.L P.γ P.δ LG1 (capH H) (Dc.capM M') (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0 := by
    intro ts k
    rw [Dc.kernelProt_cap, Dc.cfg_fix_cap, kernelProt_port_term _ _ _ Dc.dec1 _ _ _ 0 (ts 1)]
  have hHk : ∀ k : Mom P.d, ‖(H ((0 : Fin 2), X.lonePath) k : ℂ)‖ₑ ≤ ENNReal.ofReal (B Dc.ℓ0.1 : ℝ) := fun k => by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp := SNormR_pointwise (H Dc.ℓ0.1) _ hβ (hH Dc.ℓ0 hℓ0) k
    refine hp.trans ?_
    calc (B Dc.ℓ0.1 : ℝ) * jbr k ^ (-((40 * P.d : ℕ) : ℝ)) ≤ (B Dc.ℓ0.1 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos (Induct.one_le_jbr k)
            (by simp)) hβ
      _ = _ := mul_one _
  have hgood : GoodMult LG1 X (Dc.capM M') := goodMult_alpha_cap Dc ω M Mu ind hind
  refine (hLOE P.L K.hL (timeBoxGt p q') b₀ c₀ _ (ENNReal.ofReal (B Dc.ℓ0.1 : ℝ) *
      ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG1 B1))) fun k _ => ?_).trans ?_
  · refine (XNorm00Restr_single_le_rn θ _ _ k).trans ?_
    rw [rn_congr θ (f' := fun ts => (H ((0 : Fin 2), X.lonePath) k : ℂ) *
      kernelProt P.L P.γ P.δ LG1 (capH H) (Dc.capM M') (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k
        (fun _ => 0) 0) fun ts _ => hker ts k]
    unfold rn
    refine (VineEstS3.Eng.XNorm00Restr_const_mul_le θ _ _ _ _).trans (mul_le_mul' (hHk k) ?_)
    have := hperk hp hn LG1 X hsh1 (hsz1 ▸ hsz) (treeAmb_of_cap hamb Dc) hne hps hsp t q' (capH H) B1 hH1
      (Dc.capM M') hgood k
    rw [hinc1]
    exact this
  · have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0 _
    have hCδr : 0 ≤ P.C₁ * P.δ * rb P (n - 1) (protIncoh X LG) := mul_nonneg (mul_nonneg hC1 K.hδ) hr
    have hR1 : 0 ≤ Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG1 B1) := by
      have := latC_nonneg P.d
      have := Real.rpow_nonneg hL0 (4 * c')
      positivity
    rw [← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)), regBound_eq_rb,
      rb_succ P hn1, ← ENNReal.ofReal_mul hLc, ← ENNReal.ofReal_mul (mul_nonneg hLc hCδr), hleafeq]
    refine ENNReal.ofReal_le_ofReal ?_
    have := term_final_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := (B Dc.ℓ0.1 : ℝ))
      (leaf := leafSizeProduct LG1 B1) (r := rb P (n - 1) (protIncoh X LG)) (c := c) (c' := c') K.hL K.hδ hC1 hCr
      hCL hβ hleaf1 hr rfl hbig hc
    calc CL * P.L ^ (31 * P.d) * ((B Dc.ℓ0.1 : ℝ) * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 *
          (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) *
            leafSizeProduct LG1 B1)))
        ≤ P.L ^ c * (P.C₁ * P.δ * rb P (n - 1) (protIncoh X LG)) * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 B1) := this
      _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
