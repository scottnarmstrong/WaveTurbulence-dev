/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.PenPre2
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFinal

/-! # D3 PROT-PIN: cap couples in `penTerm` with a nonempty prefix and in `termChild`

`capc_pen_pre_perk`/`capc_pen_pre_final`: (P4) with a prefix (the paired tree's `pen_pre_perk`, a `StarMult` on the
pulled data). `capc_termChild_final_of`: (P7) for cap couples, conditional on the TChild worker's `TcTraceU` exactly as
its tree final `tc_termChild_final_of` (the paired tree's `tc_perk_red`/`tc_perk_green`). The terminal node is
designated in both, so the port time of the paired tree is irrelevant (`capc_port_ts`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The pulled multiplier of the paired tree is a `StarMult` with the pulled star cost. -/
theorem capc_starMult {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {d : ℕ} {L : ℝ}
    (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    StarMult L LG1 X (capcMult Dc S ω F M Fu Mu ind) (starCost (capcS Dc S) (fun z => cω (capι Dc z))) := by
  rw [capcMult_eq]
  exact starMult_tree (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres)
    (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y))
    (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind)

/-- **(P4) with a prefix for a cap couple, one output.** -/
theorem capc_pen_pre_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') (_hC11 : 1 ≤ P.C₁) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
      {m : MiniTreeCode} {Qr Qg : RegCpl} (_Dc : CapData (appendChain Xp (cpair m Qr Qg .nil)) LG LG1)
      (_C : CutTermData LG1 Xp m Qr Qg .nil LGp LGi LGr LGg) (_hXp : Xp ≠ .nil)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg .nil)) LG1)
      (_hsz : (appendChain Xp (cpair m Qr Qg .nil)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg .nil)) LG1) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg .nil)) ind) (k : Mom P.d),
      rn θ (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg .nil)) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG1)
          (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨C5, hC5, hp5⟩ := pen_pre_perk hθ0 hθ1
  refine ⟨C5.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc hC11 p hp n hn LG LG1 LGp LGi LGr LGg Xp m Qr Qg Dc C hXp hsh hsz hamb s hps hsp
    t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : appendChain Xp (cpair m Qr Qg .nil) ≠ .nil := appendChain_ne_nil _ _ _ _ _
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set R : ℝ := twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG1)
    (leafSizeProduct LG1 (capcB B)) (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := twoRb_nonneg hC1 K.hδ hL0 _ _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg .nil)) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (C5.toReal * R) := by
    rw [rn_congr θ fun ts _ => capc_port_ts Dc .penTerm (Or.inr (Or.inl rfl)) P.L P.γ P.δ (capH H) _ s t ts k,
      box_of_pinsRoot_false (pen_pinsRoot_pre hXp m Qr Qg), ← mul_ofReal_toReal hC5 hR0]
    exact hp5 K hθc hC11 hp hn C hXp hsh hsz hamb hps hsp t q' (capH H) (capcB B) (capc_leafwise Dc hH) _ _
      (capc_starMult Dc S ω cω hpres F M hM Fu Mu hMu ind hind) k
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (appendChain Xp (cpair m Qr Qg .nil)).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ =>
    capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .penTerm s t ts k)).trans (hcap.trans (le_of_eq ?_))
  rw [hR, twoRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **(P4) with a prefix for protected cap couples in `X^{θ,30d,0}`** (`θ` with `c' = 0`). -/
theorem capc_pen_pre_final {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) {Xp : RegChain}
      {m : MiniTreeCode} {Qr Qg : RegCpl} (_hXp : Xp ≠ .nil)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg .nil)) LG)
      (_hsz : protSize (appendChain Xp (cpair m Qr Qg .nil)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain Xp (cpair m Qr Qg .nil)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg .nil)) ind) (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg .nil)) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C1, hC1, hperk⟩ := capc_pen_pre_perk hθ0 hθ1
  refine ⟨C1, hC1, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG Xp m Qr Qg hXp hsh hsz hamb s hps hsp t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind b₀ c₀
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  have hC1' : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  have hX : (appendChain Xp (cpair m Qr Qg .nil)).size = 2 * n := by rw [← hsz, hsz1]; rfl
  have hn2 : 2 ≤ n := by
    obtain ⟨np, _, _, _, hnp, -, -, -, h⟩ := cut_sizes hX
    have := pen_size_two Xp (pen_lonePath_ne hXp)
    omega
  rw [prod_ofReal_starCost, hinc1]
  obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG1 Xp m Qr Qg .nil hsh1.2.1 hsh1.1
  exact final_two K.hL K.hδ hC1' hC1 hCL (a := 7 * 0) (by norm_num) hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf hCS fun k =>
    hperk K hθc hC11 hp hn Dc C hXp hsh1 hX hamb1 hps hsp t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k

end WaveTurbulence.Flower.ProtPin
