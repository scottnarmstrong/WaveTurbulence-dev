/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2m

/-! # D3 PROT-PIN (P7): (c−), the partner port in layer `p`

`tc_t2m_move`: the root trace of `type2 Xp nil (type1 c Q₁ Q₂ Q₃)` (traced root of tree `1` in layer `p`), the lone
port of the chain tree also in layer `p`: the partner time ranges over `(p, y)` (`tc_t2mU_move`), the terminal kink
`tc_kink0` (as `tc_t1_move`) with the chain tree `K_X(y, u)` as an extra factor (`tc_tree_mixed` on
`timeBoxGt p p ⊇ triS p p`); the root link of `Q_lp` is coherent. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **(c−), the partner port in layer `p`.** -/
theorem tc_t2m_move {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) (_hθc : PieceLoss P θ 0) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGX : LayeredGarden 1}
      {LGQ LG₁ LG₂ LG₃ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
      (h : T1Data c Q₁ Q₂ Q₃ LGQ.garden LG₁.garden LG₂.garden LG₃.garden)
      (_hdQ : (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes LGQ.garden)
      (_hlA : ∀ z, LG₁.layer z = LGQ.layer (h.ιA z)) (_hlB : ∀ z, LG₂.layer z = LGQ.layer (h.ιB z))
      (_hlC : ∀ z, LG₃.layer z = LGQ.layer (h.ιC z))
      (_hwf : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).wf = true)
      (_hsz : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).size = 2 * n)
      (_hdec : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden) (_hle : ∀ a, LG.layer a ≤ p)
      (_hA : TcCplAmbS p (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)) LG)
      (_hj : layerAt LG ((1 : Fin 2), []) = p) (_heq : layerAt LG ((0 : Fin 2), Xp.lonePath) = p)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LG Hr Br)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      rn θ (win p) (fun y => kernelProt P.L P.γ P.δ LG Hr
          (gateM S ω F M Fu Mu) (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links)) *
            leafSizeProduct LG Br * starCost S cω)) * tcWt P.L k := by
  obtain ⟨C₀, hC₀, hkink⟩ := tc_kink0 hθ0 (by linarith)
  set Tr := Regref.traceConst (r := 2) θ VineEstS3.chiUnit with hTr
  have hTrf : Tr < ⊤ := traceConst_lt_top θ
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  have hT4f : T4 < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  set Ck : ℝ≥0∞ := ENNReal.ofReal C₀ * (ENNReal.ofReal (2 ^ θ) * (T4 * (Tr * (Tr * Tr)))) with hCk
  have hCkf : Ck < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top hT4f (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top hTrf hTrf))))
  refine ⟨Ck, hCkf, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC hθc p hp n hn LG Xp c Q₁ Q₂ Q₃ LGX LGQ LG₁ LG₂ LG₃ D h hdQ hlA hlB hlC hwf hsz
    hdec hle hA hj heq s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  obtain ⟨hwX, hwQ⟩ := tc2_wf hwf
  obtain ⟨hw₁, hw₂, hw₃⟩ := tc_t1_wf hwQ
  obtain ⟨nX, n₁, n₂, n₃, hnX, hn₁, hn₂, hn₃, hnsum⟩ := tc2_sizes hsz
  have hXne : Xp ≠ .nil := by
    rintro rfl
    simp [RegCpl.wf, RegChain.isNil] at hwf
  have hr : ∀ t : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree t).branching := by
    intro t
    fin_cases t
    · exact tc2_root0 D hXne
    · have := (D.gd.bot_iff ((1 : Fin 2), [])).2.2.2 (h.root_mem 1)
      simpa [botAddr] using this
  obtain ⟨hHX, hHQ⟩ := tc2_leafwise D hHr
  obtain ⟨hH₁, hH₂, hH₃⟩ := tc_t1_leafwise h hHQ
  have hleA := layerAt_le_of_forall_layer_le hle
  -- layers
  set 𝔏 : ℕ := layerAt LG ((0 : Fin 2), Xp.lonePath) with h𝔏
  have h𝔏e : 𝔏 = p := heq
  have hleX : ∀ a, LGX.layer a ≤ p := fun a => by rw [D.layX]; exact hleA _
  have hleQ : ∀ a, LGQ.layer a ≤ p := fun a => by rw [D.layQ]; exact hleA _
  have hle₁ : ∀ a, LG₁.layer a ≤ p := fun a => by rw [hlA]; exact hleQ _
  have hle₂ : ∀ a, LG₂.layer a ≤ p := fun a => by rw [hlB]; exact hleQ _
  have hle₃ : ∀ a, LG₃.layer a ≤ p := fun a => by rw [hlC]; exact hleQ _
  have hq0 : layerAt LGQ ((0 : Fin 2), []) = 𝔏 := by
    rw [tc2_layerAt_Q D _ (TTree.branching_subset_nodes _ (h.root_mem 0))]
    simp [botAddr, h𝔏]
  have hq1 : layerAt LGQ ((1 : Fin 2), []) = p := by
    rw [tc2_layerAt_Q D _ (TTree.branching_subset_nodes _ (h.root_mem 1))]
    simpa [botAddr] using hj
  have hrA : ∀ t : Fin 2, LG₁.layer (GNode.root LG₁.garden.tree t) ≤ layerAt LGQ (t, []) := fun t => by
    rw [hlA]; exact tc_child_le LGQ hleQ _ t (slotA c t) rfl
  have hrB : ∀ t : Fin 2, LG₂.layer (GNode.root LG₂.garden.tree t) ≤ layerAt LGQ (t1sw t, []) := fun t => by
    rw [hlB]; exact tc_child_le LGQ hleQ _ (t1sw t) 1 rfl
  have hrC : ∀ t : Fin 2, LG₃.layer (GNode.root LG₃.garden.tree t) ≤ layerAt LGQ (t, []) := fun t => by
    rw [hlC]; exact tc_child_le LGQ hleQ _ t (slotC c t) rfl
  have hrX : LGX.layer (GNode.root LGX.garden.tree 0) ≤ p := hleX _
  have hloneX : ∀ a : GNode LGX.garden.tree, a.1.2 = Xp.lonePath → LGX.layer a = 𝔏 := fun a ha => by
    rw [D.layX, ha]
  -- coherence
  have hcX := tc2_treeCoh D hdec hwX hA
  obtain ⟨w', H', a', b', hcan', hE', hsa', hsb', hlay'⟩ := tc2_cplAmbQ D hA
  obtain ⟨hc₁, hc₂, hc₃⟩ := tc_t1_cohR h hlA hlB hlC hwQ hcan' hE' hsa' hsb' hlay'
  rw [hq0, hq1, h𝔏e] at hc₁ hc₂ hc₃
  -- multipliers
  set SQ := pullS D.gd.ι₂ S with hSQ
  set ωQ : GNode LGQ.garden.tree → Flower.IncTop.Star P.d → ℂ := fun z => ω (D.gd.ι₂ z) with hωQ
  set cQ : GNode LGQ.garden.tree → ℝ := fun z => cω (D.gd.ι₂ z) with hcQ
  set FQ := pullF (fun y => D.gd.ofSum (.inr y)) F with hFQ
  set MQf : GBranch LGQ.garden.tree → ℝ := fun y => M (D.gd.ofSum (.inr y)) with hMQf
  set FuQ := pullF (fun y => D.gd.ofSum (.inr y)) Fu with hFuQ
  set MuQ : GBranch LGQ.garden.tree → ℝ := fun y => Mu (D.gd.ofSum (.inr y)) with hMuQ
  have hpQ : ∀ a ∈ SQ, Flower.IncTop.StarPresented (30 * P.d) (ωQ a) (cQ a) := pull_pres _ hpres
  have hMQs : ∀ b ∈ FQ, P.L ≤ MQf b := pull_scale _ hM
  have hMuQs : ∀ b ∈ FuQ, P.L ≤ MuQ b := pull_scale _ hMu
  have hMg := tc2_mult D hr S ω F M Fu Mu
  have hMQ := tc_t1_mult h SQ ωQ FQ MQf FuQ MuQ
  set mX := pullMult D.gd.ι₁ (fun x => D.gd.ofSum (.inl x)) S ω F M Fu Mu with hmX
  set m₁ := pullMult h.ιA h.βA SQ ωQ FQ MQf FuQ MuQ with hm₁
  set m₂ := pullMult h.ιB h.βB SQ ωQ FQ MQf FuQ MuQ with hm₂
  set m₃ := pullMult h.ιC h.βC SQ ωQ FQ MQf FuQ MuQ with hm₃
  have hGX := pull_pres (J := 30 * P.d) D.gd.ι₁ hpres
  have hG₁ := pull_pres (J := 30 * P.d) h.ιA hpQ
  have hG₂ := pull_pres (J := 30 * P.d) h.ιB hpQ
  have hG₃ := pull_pres (J := 30 * P.d) h.ιC hpQ
  have hmXB := FiltCoh.norm_d5Mult_le (pullS D.gd.ι₁ S) (fun z => ω (D.gd.ι₁ z)) (fun z => cω (D.gd.ι₁ z)) hGX
    (pullF (fun x => D.gd.ofSum (.inl x)) F) (fun _ => false) (fun y => M (D.gd.ofSum (.inl y)))
    (pullF (fun x => D.gd.ofSum (.inl x)) Fu) (fun y => Mu (D.gd.ofSum (.inl y)))
  have hm₁B := FiltCoh.norm_d5Mult_le (pullS h.ιA SQ) (fun z => ωQ (h.ιA z)) (fun z => cQ (h.ιA z)) hG₁
    (pullF h.βA FQ) (fun _ => false) (fun y => MQf (h.βA y)) (pullF h.βA FuQ) (fun y => MuQ (h.βA y))
  have hm₂B := FiltCoh.norm_d5Mult_le (pullS h.ιB SQ) (fun z => ωQ (h.ιB z)) (fun z => cQ (h.ιB z)) hG₂
    (pullF h.βB FQ) (fun _ => false) (fun y => MQf (h.βB y)) (pullF h.βB FuQ) (fun y => MuQ (h.βB y))
  have hm₃B := FiltCoh.norm_d5Mult_le (pullS h.ιC SQ) (fun z => ωQ (h.ιC z)) (fun z => cQ (h.ιC z)) hG₃
    (pullF h.βC FQ) (fun _ => false) (fun y => MQf (h.βC y)) (pullF h.βC FuQ) (fun y => MuQ (h.βC y))
  set Ca : ℝ := costB SQ cQ (h.rt 0) * costB SQ cQ (h.rt 1) with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)
  have hMc : ∀ A B : Fin 4 → Mom P.d, ‖fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 0) A *
      fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 1) B‖ ≤ Ca := fun A B => by
    rw [norm_mul]
    exact mul_le_mul (norm_fD3'_le SQ ωQ cQ hpQ FQ MQf FuQ MuQ _ _) (norm_fD3'_le SQ ωQ cQ hpQ FQ MQf FuQ MuQ _ _)
      (norm_nonneg _) (costB_nonneg _ _ _)
  set BX : ℝ := (∏ a ∈ pullS D.gd.ι₁ S, max (cω (D.gd.ι₁ a)) 0) *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl x)) F).card *
    FiltCoh.chiDSup ^ (pullF (fun x => D.gd.ofSum (.inl x)) Fu).card with hBX
  set B₁ : ℝ := (∏ a ∈ pullS h.ιA SQ, max (cQ (h.ιA a)) 0) * FiltCoh.chiDSup ^ (pullF h.βA FQ).card *
    FiltCoh.chiDSup ^ (pullF h.βA FuQ).card with hB₁
  set B₂ : ℝ := (∏ a ∈ pullS h.ιB SQ, max (cQ (h.ιB a)) 0) * FiltCoh.chiDSup ^ (pullF h.βB FQ).card *
    FiltCoh.chiDSup ^ (pullF h.βB FuQ).card with hB₂
  set B₃ : ℝ := (∏ a ∈ pullS h.ιC SQ, max (cQ (h.ιC a)) 0) * FiltCoh.chiDSup ^ (pullF h.βC FQ).card *
    FiltCoh.chiDSup ^ (pullF h.βC FuQ).card with hB₃
  set CM : ℝ := max BX (max Ca (max B₁ (max B₂ B₃))) with hCMd
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun i : Fin P.d → ℤ => |Hr ℓ.1 (k' + latticePoint P.L i)| :=
    fun ℓ hℓ k' => summable_coset_piece hHr hL1 k' ℓ hℓ
  have hle_n : ∀ i, i ≤ n → i ≤ P.N (p + 1) ^ 4 := fun i hi => hi.trans hn
  -- the identity, the partner time in `(p, y)`
  set ζ : ℤˣ := LGQ.garden.sig 1 with hζ
  have hid : ∀ T : ℝ, T ≤ p + 1 → kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 1 then s else T) 0 (trFix 1 s) k (fun _ => 0) 0 =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' e : T1E P.d,
        (fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 0) (t1Star c P.L k e 0) *
          fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        ∫ u in Ioo (p : ℝ) T, t1Ph ζ P.L P.γ P.δ k e s u *
          (kernelProt P.L P.γ P.δ LGX (t2HX Hr) mX (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
                (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
              (kernelProt P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) m₂ (fun x => t1Clock 1 s u (t1sw x.1.1)) 0
                  (fun _ => none) (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
                kernelProt P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun x => t1Clock 1 s u x.1.1) 0
                  (fun _ => none) (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0))) := by
    intro T hT
    set U : Fin 2 → ℝ := fun t => if t = 1 then s else T with hU
    have hU0 : U 0 = T := by simp [hU]
    have hid0 := D.kernelProt_t2m h hlA hlB hlC P.L P.γ P.δ Hr hHs (gateM S ω F M Fu Mu) mX
      (pullMult D.gd.ι₂ (fun y => D.gd.ofSum (.inr y)) S ω F M Fu Mu) _ m₁ m₂ m₃ hMg hMQ CM
      (fun κ => (hmXB κ).trans (le_max_left _ _))
      (fun A B => (hMc A B).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hm₁B κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hm₂B κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      (fun κ => (hm₃B κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      U 0 s (by simp [hU]) k
    rw [hU0, tc_t2mU_move heq hT] at hid0
    exact hid0
  -- the chain tree
  set G : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGX (t2HX Hr) (fun _ => x 0) (x 1) k
    (fun _ => 0) 0 mX with hG
  have hGc : Continuous G := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGX (t2HX Hr) D.decX mX BX hmXB k
    (summable_coset_piece hHX hL1 k)
  have hKX : ∀ T u : ℝ, kernelProt P.L P.γ P.δ LGX (t2HX Hr) mX (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 =
      G ![T, u] := fun T u => by
    rw [cut_kernel_tree_m P.L P.γ P.δ LGX D.decX (t2HX Hr) mX T u k]
    rfl
  set bX : ℝ := P.L ^ (0 : ℝ) * rb P nX (LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) *
    leafSizeProduct LGX (tc2BX Br) * starCost (pullS D.gd.ι₁ S) (fun z => cω (D.gd.ι₁ z)) with hbX
  have hloneXp : ∀ a : GNode LGX.garden.tree, a.1.2 = Xp.lonePath → LGX.layer a = p := fun a ha => by
    rw [hloneX a ha, h𝔏e]
  have hcXp : LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) = 0 → IsCoherentTreeAt p p p Xp LGX := fun h0 => by
    have := hcX h0; rwa [show layerAt LG ((0 : Fin 2), Xp.lonePath) = p from heq] at this
  have hGb : rn θ (timeBoxGt (p : ℝ) p) G ≤ ENNReal.ofReal bX := by
    rw [hbX, ← piece_conv hL0 hrb _ _ 0 nX _ _]
    exact tc_tree_mixed K hFC hp (hle_n nX (by omega)) hθc Xp LGX hwX hnX D.decX hleX (q := p) (q' := p)
      le_rfl le_rfl hrX hloneXp hcXp _ _ _ hGX _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHX k
  have hGt : rn θ (triS (p : ℝ) p) G ≤ ENNReal.ofReal bX := (rn_mono_set θ (triS_subset _ _) G).trans hGb
  -- the sub-couple pieces
  have hrA0 : LG₁.layer (GNode.root LG₁.garden.tree 0) ≤ p := (hrA 0).trans (hq0.trans h𝔏e).le
  have hrA1 : LG₁.layer (GNode.root LG₁.garden.tree 1) ≤ p := (hrA 1).trans hq1.le
  have hrC0 : LG₃.layer (GNode.root LG₃.garden.tree 0) ≤ p := (hrC 0).trans (hq0.trans h𝔏e).le
  have hrC1 : LG₃.layer (GNode.root LG₃.garden.tree 1) ≤ p := (hrC 1).trans hq1.le
  have e0 : t1sw (0 : Fin 2) = 1 := by decide
  have e1 : t1sw (1 : Fin 2) = 0 := by decide
  have hrB0 : LG₂.layer (GNode.root LG₂.garden.tree 0) ≤ p := by
    have := hrB 0; rw [e0, hq1] at this; exact this
  have hrB1 : LG₂.layer (GNode.root LG₂.garden.tree 1) ≤ p := by
    have := hrB 1; rw [e1, hq0, h𝔏e] at this; exact this
  set Bf : T1E P.d → ℝ := fun e => ((ζ : ℤ) : ℝ) * t1Freq P.L P.γ P.δ k e with hBf
  set f₁ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr))
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.1) (fun _ => 0) 0 m₁ with hf₁d
  set f₂ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr))
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 m₂ with hf₂d
  set f₃ : T1E P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr))
    (fun z => if z.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 m₃ with hf₃d
  have hf₁c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₁ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) h.dec₁.1.1 m₁ B₁ hm₁B _
      (summable_coset_piece hH₁ hL1 _)
  have hf₂c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₂ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) h.dec₂.1.1 m₂ B₂ hm₂B _
      (summable_coset_piece hH₂ hL1 _)
  have hf₃c : ∀ e, Continuous (fun x : Fin 2 → ℝ => f₃ e (x 0) (x 1)) := fun e =>
    FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) h.dec₃.1.1 m₃ B₃ hm₃B _
      (summable_coset_piece hH₃ hL1 _)
  set g₁ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₁ e (tcOr 1 s (x 1) 0) (tcOr 1 s (x 1) 1) with hg₁
  set g₂ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₂ e (tcOrB 1 s (x 1) 0) (tcOrB 1 s (x 1) 1) with hg₂
  set g₃ : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => f₃ e (tcOr 1 s (x 1) 0) (tcOr 1 s (x 1) 1) with hg₃
  have hgc : ∀ (f : ℝ → ℝ → ℂ) (o : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, o u v 0 = u ∧ o u v 1 = v) ∨ (∀ u v, o u v 0 = v ∧ o u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (o s (x 1) 0) (o s (x 1) 1)) := by
    intro f o ho hf
    have := tc_oriented_cont o ho hf
    exact this.comp (show Continuous fun x : Fin 2 → ℝ => ![s, x 1] by fun_prop)
  have hg₁c : ∀ e, Continuous (g₁ e) := fun e => hgc _ _ (tcOr_cases 1) (hf₁c e)
  have hg₂c : ∀ e, Continuous (g₂ e) := fun e => hgc _ _ (tcOrB_cases 1) (hf₂c e)
  have hg₃c : ∀ e, Continuous (g₃ e) := fun e => hgc _ _ (tcOr_cases 1) (hf₃c e)
  set g : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => g₁ e x * (g₂ e x * g₃ e x) with hgd
  have hgcc : ∀ e, Continuous (g e) := fun e => (hg₁c e).mul ((hg₂c e).mul (hg₃c e))
  set hh : T1E P.d → (Fin 2 → ℝ) → ℂ := fun e x => G x * g e x with hhh
  have hhc : ∀ e, Continuous (hh e) := fun e => hGc.mul (hgcc e)
  set b₁ : ℝ := P.L ^ (0 : ℝ) * rb P n₁ (LG₁.incoherency Q₁.links) * leafSizeProduct LG₁ (tcBA c (tc2BQ Xp Br)) *
    starCost (pullS h.ιA SQ) (fun z => cQ (h.ιA z)) with hb₁
  set b₂ : ℝ := P.L ^ (0 : ℝ) * rb P n₂ (LG₂.incoherency Q₂.links) * leafSizeProduct LG₂ (tcBB (tc2BQ Xp Br)) *
    starCost (pullS h.ιB SQ) (fun z => cQ (h.ιB z)) with hb₂
  set b₃ : ℝ := P.L ^ (0 : ℝ) * rb P n₃ (LG₃.incoherency Q₃.links) * leafSizeProduct LG₃ (tcBC c (tc2BQ Xp Br)) *
    starCost (pullS h.ιC SQ) (fun z => cQ (h.ιC z)) with hb₃
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hp1 : ∀ e, rn θ (timeBox (p : ℝ) p) (fun x => f₁ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₁, ← piece_conv hL0 hrb _ _ 0 n₁ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₁ (by omega)) hθc Q₁ LG₁ hw₁ hn₁ h.dec₁ hle₁ le_rfl le_rfl hrA0 hrA1
      hc₁ _ _ _ hG₁ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₁ _
  have hp2 : ∀ e, rn θ (timeBox (p : ℝ) p) (fun x => f₂ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₂, ← piece_conv hL0 hrb _ _ 0 n₂ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₂ (by omega)) hθc Q₂ LG₂ hw₂ hn₂ h.dec₂ hle₂ le_rfl le_rfl hrB0 hrB1
      hc₂ _ _ _ hG₂ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₂ _
  have hp3 : ∀ e, rn θ (timeBox (p : ℝ) p) (fun x => f₃ e (x 0) (x 1)) ≤
      ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) := fun e => by
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₃, ← piece_conv hL0 hrb _ _ 0 n₃ _ _]
    exact tc_couple_mixed K hFC hp (hle_n n₃ (by omega)) hθc Q₃ LG₃ hw₃ hn₃ h.dec₃ hle₃ le_rfl le_rfl hrC0 hrC1
      hc₃ _ _ _ hG₃ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₃ _
  have hps' : (p : ℝ) ≤ s := hps.le
  have hsp' : s ≤ (p : ℝ) + 1 := hsp.le
  have ht1 : ∀ e, rn θ (triS (p : ℝ) p) (g₁ e) ≤ Tr * (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1))) :=
    fun e => (tc_piece_trace hθ0 hps' hsp' (f₁ e) (tcOr 1) (tcOr_cases 1) (hf₁c e)).trans (mul_le_mul' le_rfl (hp1 e))
  have ht2 : ∀ e, rn θ (triS (p : ℝ) p) (g₂ e) ≤ Tr * (ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) :=
    fun e => (tc_piece_trace hθ0 hps' hsp' (f₂ e) (tcOrB 1) (tcOrB_cases 1) (hf₂c e)).trans (mul_le_mul' le_rfl (hp2 e))
  have ht3 : ∀ e, rn θ (triS (p : ℝ) p) (g₃ e) ≤ Tr * (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) :=
    fun e => (tc_piece_trace hθ0 hps' hsp' (f₃ e) (tcOr 1) (tcOr_cases 1) (hf₃c e)).trans (mul_le_mul' le_rfl (hp3 e))
  have hf1 : ∀ e, rn θ (triS (p : ℝ) p) (g₁ e) < ⊤ := fun e => (ht1 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hf2 : ∀ e, rn θ (triS (p : ℝ) p) (g₂ e) < ⊤ := fun e => (ht2 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have hf3 : ∀ e, rn θ (triS (p : ℝ) p) (g₃ e) < ⊤ := fun e => (ht3 e).trans_lt
    (ENNReal.mul_lt_top hTrf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))
  have h23 : ∀ e, rn θ (triS (p : ℝ) p) (fun x => g₂ e x * g₃ e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (triS (p : ℝ) p) (g₂ e) * rn θ (triS (p : ℝ) p) (g₃ e) := fun e =>
    rn_mul_le hθ0 (triS_closure p p) (g₂ e) (g₃ e) (hg₃c e) (hf2 e) (hf3 e)
  have hf23 : ∀ e, rn θ (triS (p : ℝ) p) (fun x => g₂ e x * g₃ e x) < ⊤ := fun e =>
    (h23 e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hf2 e)) (hf3 e))
  have hgb : ∀ e, rn θ (triS (p : ℝ) p) (g e) ≤ T4 * (Tr * (Tr * Tr)) *
      (ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃) *
        (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) := fun e => by
    refine (rn_mul_le hθ0 (triS_closure p p) (g₁ e) (fun x => g₂ e x * g₃ e x) ((hg₂c e).mul (hg₃c e))
      (hf1 e) (hf23 e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (triS (p : ℝ) p) (g₁ e) * rn θ (triS (p : ℝ) p) (fun x => g₂ e x * g₃ e x)
        ≤ ENNReal.ofReal (2 ^ θ) * (Tr * (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)))) *
          (ENNReal.ofReal (2 ^ θ) * (Tr * (ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)))) *
            (Tr * (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))))) :=
          mul_le_mul' (mul_le_mul' le_rfl (ht1 e)) ((h23 e).trans (mul_le_mul' (mul_le_mul' le_rfl (ht2 e)) (ht3 e)))
      _ = _ := by rw [hT4]; ring
  have hgfin : ∀ e, rn θ (triS (p : ℝ) p) (g e) < ⊤ := fun e => (hgb e).trans_lt (by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hT4f (ENNReal.mul_lt_top hTrf
      (ENNReal.mul_lt_top hTrf hTrf))) ?_) ?_ <;>
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
  have hGfin : rn θ (triS (p : ℝ) p) G < ⊤ := hGt.trans_lt ENNReal.ofReal_lt_top
  have hhb : ∀ e, rn θ (triS (p : ℝ) p) (hh e) ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bX *
      (T4 * (Tr * (Tr * Tr)) * (ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃) *
        (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) *
          ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) := fun e =>
    (rn_mul_le hθ0 (triS_closure p p) G (g e) (hgcc e) hGfin (hgfin e)).trans
      (mul_le_mul' (mul_le_mul' le_rfl hGt) (hgb e))
  have hhfin : ∀ e, rn θ (triS (p : ℝ) p) (hh e) < ⊤ := fun e => (hhb e).trans_lt (by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ?_
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hT4f (ENNReal.mul_lt_top hTrf
      (ENNReal.mul_lt_top hTrf hTrf))) ?_) ?_ <;>
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)
  -- the coefficients and the identity on the window
  set cc : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 with hcc
  set a : T1E P.d → ℂ := fun e => cc * ((fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 0) (t1Star c P.L k e 0) *
    fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
      Complex.exp (((Real.pi * Bf e * (s - p) : ℝ) : ℂ) * Complex.I)) with ha
  have hwin : ∀ y ∈ win (p : ℝ), kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k (fun _ => 0) 0 =
      ∑' e, a e * ∫ u in Ioo (p : ℝ) (y 0), cutMod (-Bf e) p u * hh e ![y 0, u] := by
    intro y hy
    rw [hid (y 0) hy.2, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    simp_rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_Ioo (a := (p : ℝ)) (b := y 0)) fun u _ => ?_
    rw [tc_t1Ph_split ζ P.L P.γ P.δ k e s p u, hKX]
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun t => t1Clock 1 s u t),
      cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB (t2HQ Xp Hr)) m₂ (fun t => t1Clock 1 s u (t1sw t)),
      cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun t => t1Clock 1 s u t)]
    simp only [ha, hcc, hhh, hgd, hg₁, hg₂, hg₃, hf₁d, hf₂d, hf₃d, tcOr, tcOrB, hBf, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    ring
  rw [rn_congr θ hwin]
  refine (hkink (T1E P.d) p p le_rfl (by linarith) (fun e => -Bf e) a hh hhc hhfin).trans ?_
  -- the exceptional sum
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  have hae : ∀ e, ‖a e‖ₑ ≤ ENNReal.ofReal (c2 * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ha]
    simp only
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hcc, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul (hMc _ _) (tc_abs_t1Eps_le c e) (abs_nonneg _) hCa0).trans
      (by rw [mul_one])) hc20
  set Z : ℝ≥0∞ := ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bX *
    (T4 * (Tr * (Tr * Tr)) * (ENNReal.ofReal b₁ * ENNReal.ofReal b₂ * ENNReal.ofReal b₃))) with hZ
  have hterm : ∀ e, ‖a e‖ₑ * rn θ (triS (p : ℝ) p) (hh e) ≤ Z * (ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) *
      ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2))) :=
    fun e => (mul_le_mul' (hae e) (hhb e)).trans (le_of_eq (by rw [hZ]; ring))
  have hsum : ∑' e, ‖a e‖ₑ * rn θ (triS (p : ℝ) p) (hh e) ≤ Z * tcWt P.L k := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl le_self_add
  calc ENNReal.ofReal C₀ * ∑' e, ‖a e‖ₑ * rn θ (triS (p : ℝ) p) (hh e)
      ≤ ENNReal.ofReal C₀ * (Z * tcWt P.L k) := mul_le_mul' le_rfl hsum
    _ ≤ _ := by
        -- the algebra
        have hg2 := tc2_incoh D hdec hdQ
        have hgQ := tc_t1_incoh h hlA hlB hlC
        rw [hq0, hq1, h𝔏e, if_pos rfl, add_zero] at hgQ
        set g := LG.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links with hgdef
        have hn1 : nX + n₁ + n₂ + n₃ = n - 1 := by omega
        have hb0 : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
            0 ≤ leafSizeProduct LGx Bx := fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
        have hb10 : 0 ≤ b₁ := by
          rw [hb₁, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
        have hb20 : 0 ≤ b₂ := by
          rw [hb₂, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
        have hb30 : 0 ≤ b₃ := by
          rw [hb₃, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
        have hbX0 : 0 ≤ bX := by
          rw [hbX, Real.rpow_zero, one_mul]; exact mul_nonneg (mul_nonneg (hrb _ _) (hb0 _ _)) (starCost_nonneg' _ _)
        have hleaf : leafSizeProduct LG Br = leafSizeProduct LGX (tc2BX Br) * (leafSizeProduct LG₁ (tcBA c (tc2BQ Xp Br)) *
            leafSizeProduct LG₂ (tcBB (tc2BQ Xp Br)) * leafSizeProduct LG₃ (tcBC c (tc2BQ Xp Br))) := by
          rw [tc2_leafSize D Br, tc_t1_leafSize h (tc2BQ Xp Br)]
        have hcost : starCost S cω = starCost (pullS D.gd.ι₁ S) (fun z => cω (D.gd.ι₁ z)) *
            (Ca * (starCost (pullS h.ιA SQ) (fun z => cQ (h.ιA z)) * (starCost (pullS h.ιB SQ) (fun z => cQ (h.ιB z)) *
              starCost (pullS h.ιC SQ) (fun z => cQ (h.ιC z))))) := by
          rw [tc2_cost D hr S cω, tc_t1_cost h SQ cQ]
        have hval : c2 * Ca * bX * (b₁ * b₂ * b₃) =
            coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br * starCost S cω := by
          have hgg : g = LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) + LG₁.incoherency Q₁.links +
              LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links := by rw [hg2, hgQ]; omega
          have h4 := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := nX) (n₂ := n₁) (n₃ := n₂) (n₄ := n₃)
            (g₁ := LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) (g₂ := LG₁.incoherency Q₁.links)
            (g₃ := LG₂.incoherency Q₂.links) (g₄ := LG₃.incoherency Q₃.links)
          have h4' : rb P nX (LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) * rb P n₁ (LG₁.incoherency Q₁.links) *
              rb P n₂ (LG₂.incoherency Q₂.links) * rb P n₃ (LG₃.incoherency Q₃.links) =
              P.C₁ ^ 3 * rb P (n - 1) g := by
            rw [h4, ← hn1, hgg]; rfl
          rw [hbX, hb₁, hb₂, hb₃, Real.rpow_zero, hleaf, hcost, hc2, ← h4']
          ring
        have hY : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br *
            starCost S cω := by
          have := starCost_nonneg' S cω
          have := hb0 LG Br
          have := hrb (n - 1) g
          positivity
        have hfin : coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br *
            starCost S cω ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) *
              leafSizeProduct LG Br * starCost S cω) := le_mul_of_one_le_left hY hL1
        have hprod : Z = ENNReal.ofReal (2 ^ θ) * (T4 * (Tr * (Tr * Tr))) * ENNReal.ofReal (c2 * Ca * bX * (b₁ * b₂ * b₃)) := by
          rw [hZ, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc20 hCa0) hbX0), ENNReal.ofReal_mul (mul_nonneg hc20 hCa0),
            ENNReal.ofReal_mul (mul_nonneg hb10 hb20), ENNReal.ofReal_mul hb10]
          ring
        rw [hprod, hval, hCk]
        calc ENNReal.ofReal C₀ * (ENNReal.ofReal (2 ^ θ) * (T4 * (Tr * (Tr * Tr))) *
              ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br *
                starCost S cω) * tcWt P.L k)
            ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (2 ^ θ) * (T4 * (Tr * (Tr * Tr))) *
              ENNReal.ofReal (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) *
                leafSizeProduct LG Br * starCost S cω)) * tcWt P.L k) :=
              mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hfin)) le_rfl)
          _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
