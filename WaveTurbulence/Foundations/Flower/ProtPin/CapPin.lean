/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapRoot
public import WaveTurbulence.Foundations.Flower.ProtPin.RootP3Bound
public import WaveTurbulence.Foundations.Flower.ProtPin.PenRoot
public import WaveTurbulence.Foundations.Flower.ProtPin.Pen5

/-! # D3 PROT-PIN: cap couples in the configurations `rootTerm` ((P2), (P3)) and `penTerm` ((P4) root-pinned, (P5)),
one output

These configurations designate the terminal node (the lone parent), so the port time of the paired tree is irrelevant
(`capc_port_irrel`, `capc_fix_pinned`); the paired tree's per-output bounds apply with the pulled star data
(`capcMult`): (P2) a constant (`pair_pack`), (P3) `p3_perk`, (P4) `pen_perk_root`, (P5) `pen5_perk` (with
`starMult_tree`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The paired tree's kernel with the port time `0` and with the port clock agree when the terminal is designated. -/
theorem capc_port_ts {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {d : ℕ}
    (Dc : CapData X LG LG1) (cfg : ProtCfg) (hcfg : cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (L γ δ : ℝ) (H1 : LeafProfiles 1 d) (m : (GNode LG1.garden.tree → Mom d) → ℂ) (s t : ℝ) (ts : Fin 2 → ℝ)
    (k : Mom d) :
    kernelProt L γ δ LG1 H1 m (fun _ => ts 0) 0 (cfg.fix X s t (ts 0)) k (fun _ => 0) 0 =
      kernelProt L γ δ LG1 H1 m (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0 :=
  capc_port_irrel L γ δ LG1 H1 m _ _ k _ _ (capc_fix_pinned Dc.dec1 cfg hcfg s t (ts 0)) 0 (ts 1)

/-- **(P2) for a cap couple, one output.** -/
theorem capc_rootTerm_pair_perk {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_Dc : CapData (cpair m Qr Qg inner) LG LG1)
      (_C : CutTermData LG1 .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG1) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG1) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (k : Mom P.d),
      rn θ (ProtCfg.rootTerm.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG B)
          (starCost S cω)) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hCf : T4 * cutNormR θ 2 < ⊤ := ENNReal.mul_lt_top hT4f (cutNormR_lt_top θ 2)
  refine ⟨(T4 * cutNormR θ 2).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGp LGi LGr LGg m Qr Qg inner Dc C hsh hsz hamb s t hps hst htp
    q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  obtain ⟨c, A, W, hWc, -, hsum, -, hrt⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb (capH H) (capcB B)
    (capc_leafwise Dc hH) (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres)
    (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y))
    (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind) k
  set V : ℂ := ∑' e, c e * (rootPh (A e) t s * W e ![t, s]) with hV
  have hconst : ∀ ts ∈ ProtCfg.rootTerm.box (cpair m Qr Qg inner) t p q',
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0 = V := by
    intro ts hts
    rw [box_rootTerm] at hts
    rw [capcMult_eq]
    exact hrt (ts 0) 0 s t hts.2 (hst.le.trans hts.2)
  have hts' : (![t, s] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) p := by
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
  have hVb : ‖V‖ₑ ≤ ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e) := by
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun e => ?_)
    rw [enorm_mul, enorm_mul, ← ofReal_norm (rootPh _ _ _), norm_rootPh, ENNReal.ofReal_one, one_mul]
    exact mul_le_mul' le_rfl (enorm_le_rn hθ0 (timeBoxGt_cl p) (hWc e) hts')
  set R : ℝ := pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := pairRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.rootTerm.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG1
      (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal ((T4 * cutNormR θ 2).toReal * R) := by
    rw [rn_congr θ hconst, box_rootTerm]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) V).trans ?_
    refine (mul_le_mul' (hVb.trans hsum) le_rfl).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCf.ne]
    exact le_of_eq (by ring)
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (cpair m Qr Qg inner).lonePath) k : ℂ) (capcStar Dc S ω k)
    _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0 (capc_input_le Dc hH k)
    (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ =>
    capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .rootTerm s t ts k)).trans (hcap.trans (le_of_eq ?_))
  rw [hR, pairRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **(P3) for a cap couple, one output.** -/
theorem capc_p3_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner rest : RegChain} (_Dc : CapData (RegChain.pair m Qr Qg inner rest) LG LG1)
      (_D : RootData LG1 m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG1)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG1) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (RegChain.pair m Qr Qg inner rest) ind) (k : Mom P.d),
      rn θ (ProtCfg.rootTerm.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * twoRb P (7 * c') n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1)
          (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨C3, hC3, hp3⟩ := p3_perk hθ0 hθ1
  refine ⟨C3.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGZ LGi LGs LGr LGg m Qr Qg inner rest Dc D hsh hsz hamb s t
    hps hst htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set R : ℝ := twoRb P (7 * c') n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := twoRb_nonneg hC1 K.hδ hL0 _ _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.rootTerm.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.rootTerm.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (C3.toReal * R) := by
    rw [rn_congr θ fun ts _ => capc_port_ts Dc .rootTerm (Or.inl rfl) P.L P.γ P.δ (capH H) _ s t ts k,
      capcMult_eq, ← mul_ofReal_toReal hC3 hR0]
    exact hp3 K hθc hp hn D hsh hsz hamb hps hst htp q' (capH H) (capcB B) (capc_leafwise Dc hH) (capcS Dc S)
      (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres) (pullF Dc.βc F) (fun y => M (Dc.βc y))
      (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y)) (pull_scale _ hMu)
      (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind) k
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (RegChain.pair m Qr Qg inner rest).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ =>
    capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .rootTerm s t ts k)).trans (hcap.trans (le_of_eq ?_))
  rw [hR, twoRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **(P4) with the root pinned for a cap couple, one output.** -/
theorem capc_pen_root_perk {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} (_Dc : CapData (appendChain .nil (cpair m Qr Qg .nil)) LG LG1)
      (_C : CutTermData LG1 .nil m Qr Qg .nil LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg .nil) LG1) (_hsz : (cpair m Qr Qg .nil).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg .nil) LG1) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain .nil (cpair m Qr Qg .nil)) ind) (k : Mom P.d),
      rn θ (ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * pairRb P c' n (protIncoh (cpair m Qr Qg .nil) LG1) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨C4, hC4, hp4⟩ := pen_perk_root hθ0
  refine ⟨C4.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGp LGi LGr LGg m Qr Qg Dc C hsh hsz hamb s t hps hst htp
    q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : appendChain .nil (cpair m Qr Qg .nil) ≠ .nil := appendChain_ne_nil _ _ _ _ _
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set R : ℝ := pairRb P c' n (protIncoh (cpair m Qr Qg .nil) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := pairRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.penTerm.box (appendChain .nil (cpair m Qr Qg .nil)) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.penTerm.fix (appendChain .nil (cpair m Qr Qg .nil)) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (C4.toReal * R) := by
    rw [rn_congr θ fun ts _ => capc_port_ts Dc .penTerm (Or.inr (Or.inl rfl)) P.L P.γ P.δ (capH H) _ s t ts k,
      capcMult_eq, ← mul_ofReal_toReal hC4 hR0]
    exact hp4 K hθc hp hn C hsh hsz hamb hps hst htp q' (capH H) (capcB B) (capc_leafwise Dc hH) (capcS Dc S)
      (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres) (pullF Dc.βc F) (fun y => M (Dc.βc y))
      (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y)) (pull_scale _ hMu)
      (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind) k
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (appendChain .nil (cpair m Qr Qg .nil)).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ =>
    capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .penTerm s t ts k)).trans (hcap.trans (le_of_eq ?_))
  rw [hR, pairRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **(P5) for a cap couple, one output.** -/
theorem capc_pen5_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
      {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
      (_Dc : CapData (appendChain Xp (cpair m Qr Qg inner)) LG LG1)
      (_C : CutTermData LG1 Xp m Qr Qg inner LGp LGi LGr LGg) (_hin : inner.lonePath ≠ [])
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG1)
      (_hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG1) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t : ℝ) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) (k : Mom P.d),
      rn θ (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg inner)) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG1)
          (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨C5, hC5, hp5⟩ := pen5_perk hθ0 hθ1
  refine ⟨C5.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGp LGi LGr LGg Xp m Qr Qg inner Dc C hin hsh hsz hamb s hps hsp
    t q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : appendChain Xp (cpair m Qr Qg inner) ≠ .nil := appendChain_ne_nil _ _ _ _ _
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  set R : ℝ := twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG1)
    (leafSizeProduct LG1 (capcB B)) (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := twoRb_nonneg hC1 K.hδ hL0 _ _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have hSM : StarMult P.L LG1 (appendChain Xp (cpair m Qr Qg inner)) (capcMult Dc S ω F M Fu Mu ind)
      (starCost (capcS Dc S) (fun z => cω (capι Dc z))) := by
    rw [capcMult_eq]
    exact starMult_tree (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres)
      (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y))
      (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind)
  have htree : rn θ (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg inner)) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (C5.toReal * R) := by
    rw [rn_congr θ fun ts _ => capc_port_ts Dc .penTerm (Or.inr (Or.inl rfl)) P.L P.γ P.δ (capH H) _ s t ts k,
      box_of_pinsRoot_false (pen_pinsRoot5 Xp m Qr Qg hin), ← mul_ofReal_toReal hC5 hR0]
    exact hp5 K hθc hp hn C hin hsh hsz hamb hps hsp t q' (capH H) (capcB B) (capc_leafwise Dc hH) _ _ hSM k
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (appendChain Xp (cpair m Qr Qg inner)).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ =>
    capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .penTerm s t ts k)).trans (hcap.trans (le_of_eq ?_))
  rw [hR, twoRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

end WaveTurbulence.Flower.ProtPin
