/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.CapMult
public import WaveTurbulence.Foundations.Flower.ProtPin.TraceP8

/-! # D3 PROT-PIN: cap couples in the configurations `root` (P1) and `trace` (P8), one output

A cap couple's kernel is the input of the cap pair, the cap's star factor (a constant) and its paired tree's kernel
with the port time `0` (`capc_kernel_eq`). The port time `0 ≤ p` is below the layer of the lone parent, so the
paired tree's root-cut identity (`pair_pack`, `root_pack`) has the range `Ioo p ·`: for `root` the kernel is a constant
(`enorm_rootInt_le`, `enorm_rootInt2_le`), for `trace` it is `mirror_low`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem capcMult_eq {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {d : ℕ}
    (Dc : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ)
    (ind : (GNode LG.garden.tree → Mom d) → ℝ) :
    capcMult Dc S ω F M Fu Mu ind = fun κ => Flower.IncTop.starWeight (capcS Dc S) (fun z => ω (capι Dc z)) κ *
      filtWeight (pullF Dc.βc F) (fun _ => false) (fun y => M (Dc.βc y)) κ *
      filtWeight (pullF Dc.βc Fu) (fun _ => false) (fun y => Mu (Dc.βc y)) κ * ((ind fun a => κ (Dc.ρ a) : ℝ) : ℂ) :=
  rfl

/-- The cap kernel at the configuration `cfg`. -/
theorem capc_kernel_cfg {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} {d : ℕ}
    (Dc : CapData X LG LG1) (hX : X ≠ .nil) (L γ δ : ℝ) (H : LeafProfiles 2 d)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star d → ℂ)
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ) (cfg : ProtCfg) (s t : ℝ)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    kernelProt L γ δ LG H (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k
        (fun _ => 0) 0 =
      (H ((0 : Fin 2), X.lonePath) k : ℂ) * capcStar Dc S ω k *
        kernelProt L γ δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
          (cfg.fix X s t (ts 0)) k (fun _ => 0) 0 := by
  rw [capc_kernel_eq Dc hX L γ δ H S ω F M Fu Mu ind, Dc.cfg_fix_cap]

/-- **`root` for a cap couple whose chain is one pair, one output.** -/
theorem capc_root_pair_perk {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_Dc : CapData (cpair m Qr Qg inner) LG LG1)
      (_C : CutTermData LG1 .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG1) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG1) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1) (s : ℝ)
      (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (k : Mom P.d),
      rn θ (ProtCfg.root.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG B)
          (starCost S cω)) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hCf : T4 * cutNormR θ 2 < ⊤ := ENNReal.mul_lt_top hT4f (cutNormR_lt_top θ 2)
  refine ⟨(T4 * cutNormR θ 2).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGp LGi LGr LGg m Qr Qg inner Dc C hsh hsz hamb t hpt htp s q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  obtain ⟨c, A, W, hWc, -, hsum, hroot, -⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb (capH H) (capcB B)
    (capc_leafwise Dc hH) (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres)
    (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y))
    (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind) k
  have D1 : PairOnly LG1 m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hlay := pair_b_layer D1 hsh.2.2.2
  set V : ℂ := ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * W e ![t, u] with hV
  have hconst : ∀ ts ∈ ProtCfg.root.box (cpair m Qr Qg inner) t p q',
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0 = V := by
    intro ts hts
    rw [box_root] at hts
    rw [capcMult_eq]
    rw [cfg_root_fix, hroot (ts 0) t 0 hts.2, rootU0_eq_low hlay htp hts.2 hp0]
  set R : ℝ := pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := pairRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.root.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG1 (capH H)
      (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0 (ProtCfg.root.fix (cpair m Qr Qg inner) s t (ts 0)) k
        (fun _ => 0) 0) ≤ ENNReal.ofReal ((T4 * cutNormR θ 2).toReal * R) := by
    rw [rn_congr θ hconst, box_root]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) V).trans ?_
    refine (mul_le_mul' ((enorm_rootInt_le hθ0 le_rfl htp.le A c W hWc).trans hsum) le_rfl).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCf.ne]
    exact le_of_eq (by ring)
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (cpair m Qr Qg inner).lonePath) k : ℂ) (capcStar Dc S ω k)
    _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0 (capc_input_le Dc hH k)
    (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ => capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .root s t ts k)).trans
    (hcap.trans (le_of_eq ?_))
  rw [hR, pairRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **`root` for a cap couple whose chain has a suffix, one output** (`ind ≡ 1`). -/
theorem capc_root_rest_perk {θ : ℝ} (hθ0 : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner rest : RegChain} (_Dc : CapData (RegChain.pair m Qr Qg inner rest) LG LG1)
      (_D : RootData LG1 m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG1)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG1) {t : ℝ} (_hpt : (p : ℝ) < t) (_htp : t < p + 1)
      (s : ℝ) (q' : ℕ) (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind1 : ∀ κ, ind κ = 1) (k : Mom P.d),
      rn θ (ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1)
          (leafSizeProduct LG B) (starCost S cω)) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hCf : T4 * cutNormR θ 2 < ⊤ := ENNReal.mul_lt_top hT4f (cutNormR_lt_top θ 2)
  refine ⟨(T4 * cutNormR θ 2).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGZ LGi LGs LGr LGg m Qr Qg inner rest Dc D hsh hsz hamb t hpt htp
    s q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hind1' : ∀ K1 : GNode LG1.garden.tree → Mom P.d, (fun K1 => ind fun a => K1 (Dc.ρ a)) K1 = 1 :=
    fun K1 => hind1 _
  obtain ⟨c, A, W, Ks, hWc, -, hKc, -, -, hlow, hsum, hroot⟩ := root_pack hθ0 K hθc hp hn D hsh hsz hamb (capH H)
    (capcB B) (capc_leafwise Dc hH) (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z))
    (capc_pres Dc hpres) (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu)
    (fun y => Mu (Dc.βc y)) (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) hind1' k
  have hlay : layerAt LG1 ((0 : Fin 1), bPath m inner) = p := by
    rw [← D.layer_bR]
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    refine hsh.2.2.2 D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
    · rw [hbp, root_lonePath]; exact List.prefix_append _ _
    · rw [hbp, root_lonePath]; simp
  set V : ℂ := ∑' e, c e * ∫ u in Ioo (p : ℝ) t, rootPh (A e) t u * (Ks ![u, (p : ℝ)] * W e ![t, u]) with hV
  have hconst : ∀ ts ∈ ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q',
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0 = V := by
    intro ts hts
    rw [box_root] at hts
    rw [capcMult_eq]
    rw [cfg_root_fix, hroot (ts 0) t 0 hts.2, rootU_eq_box hlay htp hts.2]
    refine tsum_congr fun e => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [hlow u 0 hp0]
  set R : ℝ := termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := termRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.root.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal ((T4 * cutNormR θ 2).toReal * R) := by
    rw [rn_congr θ hconst, box_root]
    refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) V).trans ?_
    refine (mul_le_mul' ((enorm_rootInt2_le hθ0 hpt.le htp.le A c Ks W hKc hWc).trans hsum) le_rfl).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCf.ne]
    exact le_of_eq (by ring)
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (RegChain.pair m Qr Qg inner rest).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ => capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .root s t ts k)).trans
    (hcap.trans (le_of_eq ?_))
  rw [hR, termRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **`trace` for a cap couple whose chain is one pair, one output.** -/
theorem capc_trace_pair_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_Dc : CapData (cpair m Qr Qg inner) LG LG1)
      (_C : CutTermData LG1 .nil m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (cpair m Qr Qg inner) LG1) (_hsz : (cpair m Qr Qg inner).size = 2 * n)
      (_hamb : TreeAmb p (cpair m Qr Qg inner) LG1) (s t : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind : TermChildIndicator (cpair m Qr Qg inner) ind)
      (k : Mom P.d),
      rn θ (ProtCfg.trace.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG B)
          (starCost S cω)) := by
  obtain ⟨Cl, hCl, hlowm⟩ := mirror_low hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hCf : Cl * cutNormR θ 2 * T4 < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hCl (cutNormR_lt_top θ 2)) hT4f
  refine ⟨(Cl * cutNormR θ 2 * T4).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGp LGi LGr LGg m Qr Qg inner Dc C hsh hsz hamb s t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  have hX : cpair m Qr Qg inner ≠ .nil := by simp [cpair]
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  obtain ⟨c, A, W, hWc, hWfin, hsum, hroot, -⟩ := pair_pack hθ0 K hθc hp hn C hsh hsz hamb (capH H) (capcB B)
    (capc_leafwise Dc hH) (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z)) (capc_pres Dc hpres)
    (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu) (fun y => Mu (Dc.βc y))
    (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) (Dc.termChild_cap ind hind) k
  have D1 : PairOnly LG1 m Qr Qg inner LGi LGr LGg := PairOnly.of_cutTerm C
  have hlay := pair_b_layer D1 hsh.2.2.2
  have hdom : ∀ ts ∈ ProtCfg.trace.box (cpair m Qr Qg inner) t p q',
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.trace.fix (cpair m Qr Qg inner) s t (ts 0)) k (fun _ => 0) 0 =
      ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0),
        rootPh (A e) (ts 0) u * ((fun _ => (1 : ℂ)) ![u, (p : ℝ)] * W e ![ts 0, u]) := by
    intro ts hts
    rw [box_trace] at hts
    rw [capcMult_eq]
    rw [cfg_trace_fix, hroot (ts 0) (ts 0) 0 le_rfl, rootU0_eq_tr_low hlay hts.1.1.2 hp0]
    simp only [one_mul]
  set R : ℝ := pairRb P c' n (protIncoh (cpair m Qr Qg inner) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := pairRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.trace.box (cpair m Qr Qg inner) t p q') (fun ts => kernelProt P.L P.γ P.δ LG1 (capH H)
      (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0 (ProtCfg.trace.fix (cpair m Qr Qg inner) s t (ts 0)) k
        (fun _ => 0) 0) ≤ ENNReal.ofReal ((Cl * cutNormR θ 2 * T4).toReal * R) := by
    rw [rn_congr θ hdom, box_trace]
    refine (hlowm (PairE m P.d) p q' A c (fun _ => 1) W continuous_const hWc (rn_one_lt_top θ p) hWfin).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCf.ne, mul_assoc]
    calc Cl * (rn θ (timeBoxGt (p : ℝ) p) (fun _ => (1 : ℂ)) * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e))
        ≤ Cl * (cutNormR θ 2 * (T4 * ENNReal.ofReal R)) := mul_le_mul' le_rfl (mul_le_mul' (rn_one_le θ p) hsum)
      _ = Cl * cutNormR θ 2 * T4 * ENNReal.ofReal R := by ring
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (cpair m Qr Qg inner).lonePath) k : ℂ) (capcStar Dc S ω k)
    _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0 (capc_input_le Dc hH k)
    (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ => capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .trace s t ts k)).trans
    (hcap.trans (le_of_eq ?_))
  rw [hR, pairRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

/-- **`trace` for a cap couple whose chain has a suffix, one output** (`ind ≡ 1`). -/
theorem capc_trace_rest_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {LG1 LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner rest : RegChain} (_Dc : CapData (RegChain.pair m Qr Qg inner rest) LG LG1)
      (_D : RootData LG1 m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG1)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG1) (s t : ℝ) (q' : ℕ)
      (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (_hind1 : ∀ κ, ind κ = 1) (k : Mom P.d),
      rn θ (ProtCfg.trace.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        ENNReal.ofReal (C * termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1)
          (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨Cl, hCl, hlowm⟩ := mirror_low hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hCf : Cl * T4 < ⊤ := ENNReal.mul_lt_top hCl hT4f
  refine ⟨(Cl * T4).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LG1 LGZ LGi LGs LGr LGg m Qr Qg inner rest Dc D hsh hsz hamb s t q'
    H B hH S ω cω hpres F M hM Fu Mu hMu ind hind1 k
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hind1' : ∀ K1 : GNode LG1.garden.tree → Mom P.d, (fun K1 => ind fun a => K1 (Dc.ρ a)) K1 = 1 :=
    fun K1 => hind1 _
  obtain ⟨c, A, W, Ks, hWc, hWfin, hKc, hKfin, -, hlow, hsum, hroot⟩ := root_pack hθ0 K hθc hp hn D hsh hsz hamb
    (capH H) (capcB B) (capc_leafwise Dc hH) (capcS Dc S) (fun z => ω (capι Dc z)) (fun z => cω (capι Dc z))
    (capc_pres Dc hpres) (pullF Dc.βc F) (fun y => M (Dc.βc y)) (pull_scale _ hM) (pullF Dc.βc Fu)
    (fun y => Mu (Dc.βc y)) (pull_scale _ hMu) (fun K1 => ind fun a => K1 (Dc.ρ a)) hind1' k
  have hlay : layerAt LG1 ((0 : Fin 1), bPath m inner) = p := by
    rw [← D.layer_bR]
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    refine hsh.2.2.2 D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
    · rw [hbp, root_lonePath]; exact List.prefix_append _ _
    · rw [hbp, root_lonePath]; simp
  have hdom : ∀ ts ∈ ProtCfg.trace.box (RegChain.pair m Qr Qg inner rest) t p q',
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0 =
      ∑' e, c e * ∫ u in Ioo (p : ℝ) (ts 0), rootPh (A e) (ts 0) u * (Ks ![u, (p : ℝ)] * W e ![ts 0, u]) := by
    intro ts hts
    rw [box_trace] at hts
    rw [capcMult_eq]
    rw [cfg_trace_fix, hroot (ts 0) (ts 0) 0 le_rfl, rootU_eq_tr hlay hts.1.1.2]
    refine tsum_congr fun e => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [hlow u 0 hp0]
  set R : ℝ := termRb P c' n (protIncoh (RegChain.pair m Qr Qg inner rest) LG1) (leafSizeProduct LG1 (capcB B))
    (starCost (capcS Dc S) (fun z => cω (capι Dc z))) with hR
  have hR0 : 0 ≤ R := termRb_nonneg hC1 K.hδ hL0 _ _ (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
    (starCost_nonneg' _ _)
  have htree : rn θ (ProtCfg.trace.box (RegChain.pair m Qr Qg inner rest) t p q') (fun ts =>
      kernelProt P.L P.γ P.δ LG1 (capH H) (capcMult Dc S ω F M Fu Mu ind) (fun _ => ts 0) 0
        (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k (fun _ => 0) 0) ≤
      ENNReal.ofReal ((Cl * T4).toReal * R) := by
    rw [rn_congr θ hdom, box_trace]
    refine (hlowm (PairE m P.d) p q' A c Ks W hKc hWc hKfin hWfin).trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCf.ne, mul_assoc]
    calc Cl * (rn θ (timeBoxGt (p : ℝ) p) Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (p : ℝ) p) (W e))
        ≤ Cl * (T4 * ENNReal.ofReal R) := mul_le_mul' le_rfl hsum
      _ = Cl * T4 * ENNReal.ofReal R := by ring
  have hcap := capc_perk (θ := θ) _ (H ((0 : Fin 2), (RegChain.pair m Qr Qg inner rest).lonePath) k : ℂ)
    (capcStar Dc S ω k) _ (NNReal.coe_nonneg _) (capcCost_nonneg Dc S cω) ENNReal.toReal_nonneg hR0
    (capc_input_le Dc hH k) (norm_capcStar_le Dc S ω cω hpres k) htree
  refine (le_of_eq (rn_congr θ fun ts _ => capc_kernel_cfg Dc hX P.L P.γ P.δ H S ω F M Fu Mu ind .trace s t ts k)).trans
    (hcap.trans (le_of_eq ?_))
  rw [hR, termRb_scale, ← capc_leaf Dc B, ← capc_cost Dc hX S cω]

end WaveTurbulence.Flower.ProtPin
