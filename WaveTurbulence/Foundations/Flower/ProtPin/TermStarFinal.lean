/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermStarCap
public import WaveTurbulence.Foundations.Flower.ProtPin.TermFinal

/-! # D3 PROT-PIN: `term` with star weights and filters, in the frozen norm

`term_tree_star_perk` (one output, explicit constant), `term_tree_final_star` and `term_cap_final_star` (the frozen norm
`X^{θ,30d,0}` on `timeBoxGt p q'` via `LocalOutputExtension`): `term_tree_final`/`term_cap_final` with a `StarMult`
multiplier and the star cost `CS` in front. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **`term` with stars and filters, protected paired tree, one output, explicit constant.** -/
theorem term_tree_star_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      (LG : LayeredGarden 1) (X : RegChain) (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n)
      (_hamb : TreeAmb p X LG) (_hne : X.lonePath ≠ []) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (t q' : ℝ)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ) (_hSM : StarMult P.L LG X Mt CS) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
          (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG B * CS)) := by
  obtain ⟨C, hC, hperk⟩ := term_star_perk hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG X hsh hsz hamb hne s hps hsp t q' H B hH Mt CS hSM k
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, LGp, LGi, LGr, LGg, D⟩ := cutTerm_pieces hsh hne
  refine (hperk K hθc hp hn D hsh hsz hamb hps hsp t q' H B hH Mt CS hSM k).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]

/-- The universal per-output bound of `term` with stars and filters (the body of `term_tree_star_perk`). -/
def TermStarPerkU (θ Cr : ℝ) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
    (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
    (LG : LayeredGarden 1) (X : RegChain) (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n)
    (_hamb : TreeAmb p X LG) (_hne : X.lonePath ≠ []) {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (t q' : ℝ)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
    (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ) (_hSM : StarMult P.L LG X Mt CS) (k : Mom P.d),
    rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
        (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG B * CS))

theorem exists_termStarPerkU {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Cr : ℝ, 0 ≤ Cr ∧ TermStarPerkU θ Cr :=
  term_tree_star_perk hθ0 hθ1

/-- The final comparison of the starred `term` bounds. -/
theorem term_star_alg {P : WTParams} {Cr CL K β CS leaf r c c' : ℝ} (hL : 1 ≤ P.L) (hδ : 0 ≤ P.δ)
    (hC1 : 0 ≤ P.C₁) (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hβ : 0 ≤ β) (hCS : 0 ≤ CS) (hleaf : 0 ≤ leaf) (hr : 0 ≤ r)
    (hK : K = CL * Cr * latC P.d ^ 2 / 4) (hbig : K * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c) :
    CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
        P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf * CS))) ≤ CS * P.L ^ c * (P.C₁ * P.δ * r) * (β * leaf) := by
  have h := term_final_alg (P := P) (Cr := Cr) (CL := CL) (K := K) (β := β * CS) (leaf := leaf) (r := r) (c := c)
    (c' := c') hL hδ hC1 hCr hCL (mul_nonneg hβ hCS) hleaf hr hK hbig hc
  calc CL * P.L ^ (31 * P.d) * (β * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
        P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf * CS)))
      = CL * P.L ^ (31 * P.d) * (β * CS * (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          P.L ^ (4 * c') * (P.C₁ ^ 3 * r) * leaf))) := by ring
    _ ≤ P.L ^ c * (P.C₁ * P.δ * r) * (β * CS * leaf) := h
    _ = _ := by ring

/-- **`term` with stars and filters in `X^{θ,30d,0}` for a protected paired tree.** -/
theorem term_tree_final_star {θ : ℝ} (_hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c Cr CL : ℝ} (hθc : PieceLoss P θ c') (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hperk : TermStarPerkU θ Cr)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : TreeAmb p X LG) (hne : X.lonePath ≠ []) {s : ℝ}
    (hps : (p : ℝ) < s) (hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 1 P.d)
    (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B) (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ)
    (CS : ℝ) (hCS : 0 ≤ CS) (hSM : StarMult P.L LG X Mt CS) (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k
        (fun _ => 0) 0) ≤
      ENNReal.ofReal CS * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
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
    (XNorm00Restr_single_le_rn θ _ _ k).trans
      (hperk K hθc hp hn LG X hsh hsz hamb hne hps hsp t q' H B hH Mt CS hSM k)).trans ?_
  have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0 _
  have hCδr : 0 ≤ P.C₁ * P.δ * rb P (n - 1) (protIncoh X LG) := mul_nonneg (mul_nonneg hC1 K.hδ) hr
  rw [← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)), regBound_eq_rb, rb_succ P hn1,
    ← ENNReal.ofReal_mul hCS, ← ENNReal.ofReal_mul (mul_nonneg hCS hLc),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCS hLc) hCδr)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := term_star_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := 1) (CS := CS)
    (leaf := leafSizeProduct LG B) (r := rb P (n - 1) (protIncoh X LG)) (c := c) (c' := c') K.hL K.hδ hC1 hCr hCL
    zero_le_one hCS hleaf hr rfl hbig hc
  simpa only [one_mul] using h

/-- **`term` with stars and filters for a protected cap couple**: its paired tree times the input of the cap pair. -/
theorem term_cap_final_star {θ : ℝ} (_hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
    (K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' c Cr CL : ℝ} (hθc : PieceLoss P θ c') (hc : 31 * (P.d : ℝ) + 4 * c' + 2 ≤ c)
    (hCr : 0 ≤ Cr) (hCL : 0 ≤ CL) (hperk : TermStarPerkU θ Cr)
    (hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d) (F : (Fin r → ℝ) → Mom P.d → ℂ)
      (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
      XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
    (hbig : termK CL Cr P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
    (hsh : ProtShape p X LG) (hsz : protSize X LG = 2 * n) (hamb : ProtAmbient p X LG) (hne : X.lonePath ≠ [])
    {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 2 P.d)
    (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind) (b₀ c₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (timeBoxGt p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨LG1, Dc, hsh1, hsz1, hinc1⟩ := cap_pieces hsh
  set M' := fun κ : GNode LG.garden.tree → Mom P.d => Flower.IncTop.starWeight S ω κ *
    filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ) with hM'
  set CS := starCost S cω with hCSdef
  have hCS : 0 ≤ CS := starCost_nonneg' S cω
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
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
  have hSM : StarMult P.L LG1 X (Dc.capM M') CS :=
    starMult_cap Dc S ω cω hpres F M hM Fu Mu hMu ind hind
  refine (hLOE P.L K.hL (timeBoxGt p q') b₀ c₀ _ (ENNReal.ofReal (B Dc.ℓ0.1 : ℝ) *
      ENNReal.ofReal (Cr * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') *
        (P.C₁ ^ 3 * rb P (n - 1) (protIncoh X LG)) * leafSizeProduct LG1 B1 * CS))) fun k _ => ?_).trans ?_
  · refine (XNorm00Restr_single_le_rn θ _ _ k).trans ?_
    rw [rn_congr θ (f' := fun ts => (H ((0 : Fin 2), X.lonePath) k : ℂ) *
      kernelProt P.L P.γ P.δ LG1 (capH H) (Dc.capM M') (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k
        (fun _ => 0) 0) fun ts _ => hker ts k]
    unfold rn
    refine (VineEstS3.Eng.XNorm00Restr_const_mul_le θ _ _ _ _).trans (mul_le_mul' (hHk k) ?_)
    have := hperk K hθc hp hn LG1 X hsh1 (hsz1 ▸ hsz) (treeAmb_of_cap hamb Dc) hne hps hsp t q' (capH H) B1 hH1
      (Dc.capM M') CS hSM k
    rw [hinc1]
    exact this
  · have hLc : 0 ≤ P.L ^ c := Real.rpow_nonneg hL0 _
    have hCδr : 0 ≤ P.C₁ * P.δ * rb P (n - 1) (protIncoh X LG) := mul_nonneg (mul_nonneg hC1 K.hδ) hr
    rw [prod_ofReal_starCost, ← hCSdef, ← ENNReal.ofReal_mul hβ,
      ← ENNReal.ofReal_mul (mul_nonneg hCL (pow_nonneg hL0 _)), regBound_eq_rb, rb_succ P hn1,
      ← ENNReal.ofReal_mul hCS, ← ENNReal.ofReal_mul (mul_nonneg hCS hLc),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCS hLc) hCδr), hleafeq]
    refine ENNReal.ofReal_le_ofReal ?_
    exact term_star_alg (P := P) (Cr := Cr) (CL := CL) (K := termK CL Cr P.d) (β := (B Dc.ℓ0.1 : ℝ)) (CS := CS)
      (leaf := leafSizeProduct LG1 B1) (r := rb P (n - 1) (protIncoh X LG)) (c := c) (c' := c') K.hL K.hδ hC1 hCr hCL
      hβ hCS hleaf1 hr rfl hbig hc

end WaveTurbulence.Flower.ProtPin
