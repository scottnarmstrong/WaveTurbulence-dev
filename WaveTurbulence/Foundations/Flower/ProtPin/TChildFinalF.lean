/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildFinal
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildPerkGF
public import WaveTurbulence.Foundations.Flower.ProtPin.CapMore
public import WaveTurbulence.Foundations.Flower.ProtPin.CapGate
public import WaveTurbulence.Foundations.Flower.ProtPin.GateF

/-! # D3 PROT-PIN (P7): `termChild` for protected paired trees and cap couples, with FILT-COH

`tc_termChild_final_ofF` / `tc_cap_termChild_final_ofF`: the forms of `tc_termChild_final_of` (TChild) and
`capc_termChild_final_of` (Cap worker, CapMore.lean; proof replayed here) with the root-trace bound `TcTraceUF`
(the prefix fact `TcFC P` and the signed ambients `ProtAmbient`, `tc_protAmb_of_cap`). `tc_cfgUF_tree_of_traceUF`,
`tc_cfgUF_cap_of_traceUF`: the `CfgUF` slices; `cfgUF_termChild_tree_of`, `cfgUF_termChild_cap_of`: the same from the
open type-2 case `TcTraceOnF θ Ct tcT2` (the type-1 cases are `tc_trace_t1F`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **(P7) for protected paired trees in `X^{θ,30d,0}`**, given the root-trace bound `TcTraceUF` of side couples. -/
theorem tc_termChild_final_ofF {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ} (_hCt : 0 ≤ Ct) (_hT : TcTraceUF θ Ct) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
      (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P) {c CL : ℝ} (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c)
      (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL (Cr * Ct * 2) P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4) (LG : LayeredGarden 1) (X : RegChain)
      (_hsh : ProtShape p X LG) (_hsz : protSize X LG = 2 * n) (_hamb : ProtAmbient p X LG) (i : Fin 3)
      (_hval : (ProtCfg.termChild i).Valid X LG p) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator X ind)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 ((ProtCfg.termChild i).box X t p q') (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix X s t (ts 0)) k (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
          ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨Cw, hCw, hred⟩ := tc_perk_redF hθ0 hθ1
  obtain ⟨Cg, hCg, hgreen⟩ := tc_perk_greenF hθ0 hθ1
  set Cm : ℝ≥0∞ := max Cw Cg with hCm
  have hCmf : Cm < ⊤ := max_lt hCw hCg
  refine ⟨Cm.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K hFC c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG X hsh hsz hamb i hval s t hps hst
    htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  obtain ⟨hne, hlast, b, hb0, hbp, hbl⟩ := hval
  obtain ⟨Xp, m, Qr, Qg, inner, rfl, LGp, LGi, LGr, LGg, D⟩ := cutTerm_pieces hsh hne
  have hsz' : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n := hsz
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
  have hbb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG.garden.tree 0).branching := by
    have h2 := b.2
    rw [show b.1.1 = 0 from Subsingleton.elim _ _, hbpath] at h2
    exact h2
  have hbL : layerAt LG ((0 : Fin 1), Xp.lonePath ++ (bPath m inner ++ [i])) = p := by
    have h1 := layerAt_node LG b.toNode
    rw [hbl] at h1
    rw [← h1]
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) hbpath.symm
  have hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg inner))
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (starCost S cω) :=
    starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind
  have hn2 : 2 ≤ n := by
    obtain ⟨np, ni, nr, ng, -, -, hnr, hng, hnsum⟩ := cut_sizes hsz'
    rcases tc_child_cases m i hi with hr | hg
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG.garden.sig 0)
      rw [← hr] at hj
      have := tc_size_pos (cut_wf D hsh.1).2.2.1 D.decR (tc_red_root_branch D hj hbb) hnr
      omega
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG.garden.sig 0)
      rw [← hg] at hj
      have := tc_size_pos (cut_wf D hsh.1).2.2.2 D.decG (tc_green_root_branch D hj hbb) hng
      omega
  -- the per-output bound in the form of `final_two`
  set Cr' : ℝ := Cm.toReal * Ct * 2 with hCr'
  have hCr'0 : 0 ≤ Cr' := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hCt) (by norm_num)
  have hleaf0 : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS0 := starCost_nonneg' S cω
  have hperk : ∀ k, rn θ ((ProtCfg.termChild i).box (appendChain Xp (cpair m Qr Qg inner)) t p q')
      (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
        (fun _ => 0) 0) ≤
      ENNReal.ofReal (Cr' * twoRb P 1 n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
        (leafSizeProduct LG B) (starCost S cω)) := by
    intro k
    have hsp : s < p + 1 := hst.trans htp
    have hbase : ∀ C : ℝ≥0∞, C ≤ Cm →
        C * ENNReal.ofReal (Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * starCost S cω))) ≤
        ENNReal.ofReal (Cr' * twoRb P 1 n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
          (leafSizeProduct LG B) (starCost S cω)) := by
      intro C hC
      have hrb := rb_nonneg hC1 K.hδ hL0 (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
      have hX0 : 0 ≤ Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * starCost S cω)) := by
        positivity
      refine (mul_le_mul' hC le_rfl).trans ?_
      rw [mul_ofReal_toReal hCmf hX0]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold twoRb
      rw [hCr', Real.rpow_one]
      have hC56 : P.C₁ ^ 6 ≤ P.C₁ ^ 6 := le_rfl
      have hY : 0 ≤ Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
            starCost S cω := by
        have := (ENNReal.toReal_nonneg : 0 ≤ Cm.toReal)
        positivity
      calc Cm.toReal * (Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
            (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
              leafSizeProduct LG B * starCost S cω)))
          = (Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
              rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
                starCost S cω) * P.C₁ ^ 6 := by ring
        _ ≤ (Cm.toReal * Ct * 2 * P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
              rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) * leafSizeProduct LG B *
                starCost S cω) * P.C₁ ^ 6 := mul_le_mul_of_nonneg_left hC56 hY
        _ = _ := by ring
    rw [box_termChild]
    rcases tc_child_cases m i hi with hr | hg
    · obtain ⟨j, hj⟩ := tc_rBase_bot m inner (LG.garden.sig 0)
      rw [← hr] at hj
      have hgn : ∀ j', gBase m inner (LG.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hr]; exact tc_gBase_ne m inner _ j'
      exact (hred hCt hT K hFC hC11 hθc hp hn D hsh hsz' hamb i j hj hgn hbb hbL hps hsp t q' H B hH
        _ _ hSM k).trans (hbase Cw (le_max_left _ _))
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG.garden.sig 0)
      rw [← hg] at hj
      have hrn : ∀ j', rBase m inner (LG.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hg]; exact tc_rBase_ne m inner _ j'
      exact (hgreen hCt hT K hFC hC11 hθc hp hn D hsh hsz' hamb i j hj hrn hbb hbL hps hsp t q' H B
        hH _ _ hSM k).trans (hbase Cg (le_max_right _ _))
  rw [prod_ofReal_starCost]
  exact final_two K.hL K.hδ hC1 hCr'0 hCL le_rfl hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf0 hCS0 hperk

/-- **(P7) for protected cap couples in `X^{θ,30d,0}`, given the side-couple root trace `TcTraceUF`** (the form of the
tree statement `tc_termChild_final_of`). -/
theorem tc_cap_termChild_final_ofF {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ} (_hCt : 0 ≤ Ct) (_hT : TcTraceUF θ Ct) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
      (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P) {c CL : ℝ} (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c)
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
  obtain ⟨Cw, hCw, hred⟩ := tc_perk_redF hθ0 hθ1
  obtain ⟨Cg, hCg, hgreen⟩ := tc_perk_greenF hθ0 hθ1
  set Cm : ℝ≥0∞ := max Cw Cg with hCm
  have hCmf : Cm < ⊤ := max_lt hCw hCg
  refine ⟨Cm.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K hFC c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG X hsh hsz hamb i hval s t hps hst
    htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := by linarith
  obtain ⟨LG1, Dc, hsh1, -, hsz1, hinc1⟩ := capc_data hsh hamb
  have hamb1 := tc_protAmb_of_cap hamb Dc
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
        C * ENNReal.ofReal (Ct * (P.L * (2 * Z * (P.C₁ ^ 6 * rb P (n - 2) g) * leafSizeProduct LG1 (capcB B) *
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
    set R : ℝ := Ct * (P.L * (2 * Z * (P.C₁ ^ 6 * rb P (n - 2) g) * leafSizeProduct LG1 (capcB B) *
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
    have hC56 : P.C₁ ^ 6 ≤ P.C₁ ^ 6 := le_rfl
    have hY : 0 ≤ Cm.toReal * Ct * 2 * P.L * Z * rb P (n - 2) g * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B)) *
        (capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z))) := by
      have := (ENNReal.toReal_nonneg : 0 ≤ Cm.toReal)
      have := starCost_nonneg' (capcS Dc S) (fun z => cω (capι Dc z))
      have := capcCost_nonneg Dc S cω
      have : 0 ≤ leafSizeProduct LG1 (capcB B) := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      have : (0 : ℝ) ≤ (B Dc.ℓ0.1 : ℝ) := NNReal.coe_nonneg _
      positivity
    calc Cm.toReal * ((B Dc.ℓ0.1 : ℝ) * capcCost Dc S cω * (Ct * (P.L * (2 * Z * (P.C₁ ^ 6 * rb P (n - 2) g) *
          leafSizeProduct LG1 (capcB B) * starCost (capcS Dc S) (fun z => cω (capι Dc z))))))
        = (Cm.toReal * Ct * 2 * P.L * Z * rb P (n - 2) g * ((B Dc.ℓ0.1 : ℝ) * leafSizeProduct LG1 (capcB B)) *
            (capcCost Dc S cω * starCost (capcS Dc S) (fun z => cω (capι Dc z)))) * P.C₁ ^ 6 := by ring
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
      exact hred hCt hT K hFC hC11 hθc hp hn D hsh1 hsz' hamb1 i j hj hgn hbb hbL hps hsp t q' (capH H) (capcB B)
        (capc_leafwise Dc hH) _ _ hSM k
    · obtain ⟨j, hj⟩ := tc_gBase_bot m inner (LG1.garden.sig 0)
      rw [← hg'] at hj
      have hrn : ∀ j', rBase m inner (LG1.garden.sig 0) j' ≠ bPath m inner ++ [i] := fun j' => by
        rw [hg']; exact tc_rBase_ne m inner _ j'
      refine hbase Cg (le_max_right _ _) k ?_
      rw [box_termChild]
      exact hgreen hCt hT K hFC hC11 hθc hp hn D hsh1 hsz' hamb1 i j hj hrn hbb hbL hps hsp t q' (capH H) (capcB B)
        (capc_leafwise Dc hH) _ _ hSM k
  rw [prod_ofReal_starCost, hinc1]
  exact final_two K.hL K.hδ hC1 hCr'0 hCL le_rfl hc hLOE hbig2 _ b₀ c₀ _ hn2 hleaf0 hCS0 hperk


theorem tc_tcFC_of {P : WTParams} {C₁c C₂c : ℝ} (hFC : FiltCoherentBoundAt { P with C₁ := C₁c, C₂ := C₂c })
    (hc0 : 0 ≤ C₁c) (hcle : C₁c ≤ P.C₁) : TcFC P := ⟨C₁c, C₂c, hFC, hc0, hcle⟩

/-- **(P7), trees, as a `CfgUF` slice**, given `TcTraceUF θ Ct`. -/
theorem tc_cfgUF_tree_of_traceUF {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ}, 0 ≤ Ct → TcTraceUF θ Ct →
      CfgUF θ (Cr * Ct * 2) (fun w _ _ cfg => w = 1 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hfin⟩ := tc_termChild_final_ofF hθ0 hθ1
  refine ⟨Cr, hCr, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b C₁c C₂c K hFC hc0 hcle hη CL hCL hC11 hLOE _hbig hbig2 p hp n hn w LG X hsh hsz
    cfg hval hamb hsel s t hps hst htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind _hind1 H B hH b₀ c₀
  obtain ⟨rfl, i, rfl⟩ := hsel
  exact hfin hCt hT K (tc_tcFC_of hFC hc0 hcle) (pieceLoss_eta hη) le_rfl hCL hC11 hLOE hbig2 hp hn LG X hsh hsz
    hamb i hval hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀

/-- **(P7), caps, as a `CfgUF` slice**, given `TcTraceUF θ Ct`. -/
theorem tc_cfgUF_cap_of_traceUF {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {Ct : ℝ}, 0 ≤ Ct → TcTraceUF θ Ct →
      CfgUF θ (Cr * Ct * 2) (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hfin⟩ := tc_cap_termChild_final_ofF hθ0 hθ1
  refine ⟨Cr, hCr, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b C₁c C₂c K hFC hc0 hcle hη CL hCL hC11 hLOE _hbig hbig2 p hp n hn w LG X hsh hsz
    cfg hval hamb hsel s t hps hst htp q' _hq' S ω cω hpres F M hM Fu Mu hMu ind hind _hind1 H B hH b₀ c₀
  obtain ⟨rfl, i, rfl⟩ := hsel
  exact hfin hCt hT K (tc_tcFC_of hFC hc0 hcle) (pieceLoss_eta hη) le_rfl hCL hC11 hLOE hbig2 hp hn LG X hsh hsz
    hamb i hval hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀

/-- `TcTraceUF` from the open type-2 case. -/
theorem tc_traceUF_of_t2 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (h2 : TcTraceOnF θ Ct tcT2) : ∃ Cm : ℝ, 0 ≤ Cm ∧ TcTraceUF θ Cm := by
  obtain ⟨C₁, hC₁, hM, hF⟩ := tc_trace_t1F hθ0 hθ1
  exact ⟨max Ct C₁, le_max_of_le_left hCt, tc_traceUF_of_cases (tcTraceOnF_mono (le_max_right _ _) hM)
    (tcTraceOnF_mono (le_max_right _ _) hF) (tcTraceOnF_mono (le_max_left _ _) h2)⟩

/-- **(P7), trees, as a `CfgUF` slice**, from the open type-2 case. -/
theorem cfgUF_termChild_tree_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (h2 : TcTraceOnF θ Ct tcT2) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr (fun w _ _ cfg => w = 1 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hcfg⟩ := tc_cfgUF_tree_of_traceUF hθ0 hθ1
  obtain ⟨Cm, hCm, hT⟩ := tc_traceUF_of_t2 hθ0 hθ1 hCt h2
  exact ⟨Cr * Cm * 2, by positivity, hcfg hCm hT⟩

/-- **(P7), caps, as a `CfgUF` slice**, from the open type-2 case. -/
theorem cfgUF_termChild_cap_of {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) {Ct : ℝ} (hCt : 0 ≤ Ct)
    (h2 : TcTraceOnF θ Ct tcT2) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ CfgUF θ Cr (fun w _ _ cfg => w = 2 ∧ ∃ i, cfg = .termChild i) := by
  obtain ⟨Cr, hCr, hcfg⟩ := tc_cfgUF_cap_of_traceUF hθ0 hθ1
  obtain ⟨Cm, hCm, hT⟩ := tc_traceUF_of_t2 hθ0 hθ1 hCt h2
  exact ⟨Cr * Cm * 2, by positivity, hcfg hCm hT⟩

end WaveTurbulence.Flower.ProtPin
