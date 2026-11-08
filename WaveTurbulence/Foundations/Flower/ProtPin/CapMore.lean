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

/-- **(P7) for protected cap couples in `X^{θ,30d,0}`, given the side-couple root trace `TcTraceU`** (the form of the
tree statement `tc_termChild_final_of`). -/
theorem capc_termChild_final_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ} (_hCt : 0 ≤ Ct) (_hT : TcTraceU θ Ct) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
      (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ} (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c)
      (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL (Cr * Ct * 2) P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 2) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : ProtAmbient p X LG) (i : Fin 3)
      (_hval : (ProtCfg.termChild i).Valid X LG p) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 ((ProtCfg.termChild i).box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨Cw, hCw, hred⟩ := tc_perk_red hθ0 hθ1
  obtain ⟨Cg, hCg, hgreen⟩ := tc_perk_green hθ0 hθ1
  set Cm : ℝ≥0∞ := max Cw Cg with hCm
  have hCmf : Cm < ⊤ := max_lt hCw hCg
  refine ⟨Cm.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG X hsh hsz hamb i hval s t hps hst
    htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  obtain ⟨LG1, Dc, hsh1, hamb1, hsz1, hinc1⟩ := capc_data hsh hamb
  obtain ⟨hne, hlast, b, hb0, hbp, hbl⟩ := Dc.cfg_valid_cap (ProtCfg.termChild i) hval
  have hXne : X ≠ .nil := ne_nil_of_lonePath hne
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, LGp, LGi, LGr, LGg, D⟩ := cutTerm_pieces hsh1 hne
  have hsz' : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n := by rw [← hsz, hsz1]; rfl
  have hlp : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (bPath m inner ++ [m.lone]) := by
    rw [appendChain_lonePath, cpair_lonePath]; rfl
  have hi : i ≠ m.lone := by
    intro h
    apply hlast
    rw [hlp, h]
    simp
  have hdrop : (appendChain Xp (cpair m Qr Qg inner)).lonePath.dropLast = Xp.lonePath ++ bPath m inner := by
    rw [hlp, ← List.append_assoc, List.dropLast_concat]
  have hbpath : b.1.2 = Xp.lonePath ++ (bPath m inner ++ [i]) := by rw [hbp, hdrop, List.append_assoc]
  have hbb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG1.garden.tree 0).branching := by
    have h2 := b.2
    rw [show b.1.1 = 0 from Subsingleton.elim _ _, hbpath] at h2
    exact h2
  have hbL : layerAt LG1 ((0 : Fin 1), Xp.lonePath ++ (bPath m inner ++ [i])) = p := by
    have h1 := layerAt_node LG1 b.toNode
    rw [hbl] at h1
    rw [← h1]
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) hbpath.symm
  have hSM : StarMult P.L LG1 (appendChain Xp (cpair m Qr Qg inner)) (capcMult Dc S ω F M Fu Mu ind)
      (starCost (capcS Dc S) (fun z => cω (capι Dc z))) :=
    capc_starMult Dc S ω cω hpres F M hM Fu Mu hMu ind hind
  have hn2 : 2 ≤ n := by
    obtain ⟨np, ni, nr, ng, -, -, hnr, hng, hnsum⟩ := cut_sizes hsz'
    rcases tc_child_cases m i hi with hr | hg
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG1.garden.sig 0)
      rw [← hr] at hj
      have := tc_size_pos (cut_wf D hsh1.1).2.2.1 D.decR (tc_red_root_branch D hj hbb) hnr
      omega
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG1.garden.sig 0)
      rw [← hg] at hj
      have := tc_size_pos (cut_wf D hsh1.1).2.2.2 D.decG (tc_green_root_branch D hj hbb) hng
      omega
  set Cr' : ℝ := Cm.toReal * Ct * 2 with hCr'
  have hCr'0 : 0 ≤ Cr' := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hCt) (by norm_num)
  have hleaf0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS0 := starCost_nonneg' S cω
  set g := protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG1 with hg
  set Z : ℝ := (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 with hZ
  -- the tree bound with the cap's leaf size and star cost
  have hbase : ∀ C : ℝ≥0∞, C ≤ Cm → ∀ k,
      rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q') (fun ts =>
        kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) (ts 1)
          ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (Ct * (P.L * (2 * Z * (P.C₁ ^ 5 * rb P (n - 2) g) * leafSizeProduct LG1 (capcB B) *
          starCost (capcS Dc S) (fun z => cω (capι Dc z))))) →
      rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q') (fun ts =>
        kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cr' * twoRb P 1 n g (leafSizeProduct LG B) (starCost S cω)) := by
    intro C hC k htr
    have hrb := rb_nonneg hC1 K.hδ hL0 (n - 2) g
    set R : ℝ := Ct * (P.L * (2 * Z * (P.C₁ ^ 5 * rb P (n - 2) g) * leafSizeProduct LG1 (capcB B) *
      starCost (capcS Dc S) (fun z => cω (capι Dc z)))) with hR
    have hR0 : 0 ≤ R := by
      have := starCost_nonneg' (capcS Dc S) (fun z => cω (capι Dc z))
      have : 0 ≤ leafSizeProduct LG1 (capcB B) := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      positivity
    have htree : rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q') (fun ts =>
        kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
          ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (Cm.toReal * R) := by
      rw [rn_congr θ fun ts _ => capc_port_ts Dc (.termChild i) (Or.inr (Or.inr ⟨i, rfl⟩)) P.L P.γ P.δ (capH H) _ s
        t ts k, ← mul_ofReal_toReal hCmf hR0]
      exact htr.trans (mul_le_mul' hC le_rfl)
    have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (appendChain Xp (cpair m Qr Qg inner)).lonePath) k : ℂ)
      (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
      (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
    refine (le_of_eq (rn_congr θ fun ts _ =>
      capc_kernel_cfg Dc hXne P.L P.γ P.δ H S ω F M Fu Mu ind (.termChild i) s t ts k)).trans (hcap.trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [capc_leaf Dc B, capc_cost Dc hXne S cω]
    unfold twoRb
    rw [hCr', hR, Real.rpow_one]
    have hC56 : P.C₁ ^ 5 ≤ P.C₁ ^ 6 := pow_le_pow_right₀ hC11 (by norm_num)
    have hY : 0 ≤ Cm.toReal * Ct * 2 * P.L * Z * rb P (n - 2) g * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B)) *
        (capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z))) := by
      have := (ENNReal.toReal_nonneg : 0 ≤ Cm.toReal)
      have := starCost_nonneg' (capcS Dc S) (fun z => cω (capι Dc z))
      have := capcCost_nonneg Dc S cω
      have : 0 ≤ leafSizeProduct LG1 (capcB B) := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      have : (0 : ℝ) ≤ (B Dc.ℓ0.1 : ℝ) := NNReal.coe_nonneg _
      positivity
    calc Cm.toReal * ((B Dc.ℓ0.1 : ℝ) * capcCost Dc S cω * (Ct * (P.L * (2 * Z * (P.C₁ ^ 5 * rb P (n - 2) g) *
          leafSizeProduct LG1 (capcB B) * starCost (capcS Dc S) (fun z => cω (capι Dc z))))))
        = (Cm.toReal * Ct * 2 * P.L * Z * rb P (n - 2) g * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B)) *
            (capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z)))) * P.C₁ ^ 5 := by ring
      _ ≤ (Cm.toReal * Ct * 2 * P.L * Z * rb P (n - 2) g * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B)) *
            (capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z)))) * P.C₁ ^ 6 :=
          mul_le_mul_of_nonneg_left hC56 hY
      _ = _ := by rw [hZ]; ring
  have hperk : ∀ k, rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q')
      (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
        (fun _ => 0) 0) ≤
      ENNReal.ofReal (Cr' * twoRb P 1 n g (leafSizeProduct LG B) (starCost S cω)) := by
    intro k
    have hsp : s < p + 1 := hst.trans htp
    rcases tc_child_cases m i hi with hr | hg'
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG1.garden.sig 0)
      rw [← hr] at hj
      have hgn : ∀ j', gBase m inner (LG1.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hr]; exact tc_gBase_ne m inner _ j'
      refine hbase Cw (le_max_left _ _) k ?_
      rw [box_termChild]
      exact hred hCt hT K hθc hp hn D hsh1 hsz' hamb1 i j hj hgn hbb hbL hps hsp t q' (capH H) (capcB B)
        (capc_leafwise Dc hH) _ _ hSM k
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG1.garden.sig 0)
      rw [← hg'] at hj
      have hrn : ∀ j', rBase m inner (LG1.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hg']; exact tc_rBase_ne m inner _ j'
      refine hbase Cg (le_max_right _ _) k ?_
      rw [box_termChild]
      exact hgreen hCt hT K hθc hp hn D hsh1 hsz' hamb1 i j hj hrn hbb hbL hps hsp t q' (capH H) (capcB B)
        (capc_leafwise Dc hH) _ _ hSM k
  rw [prod_ofReal_starCost, hinc1]
  exact final_two K.hL K.hδ hC1 hCr'0 hCL le_rfl hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf0 hCS0 hperk

end WaveTurbulence.Flower.ProtPin
