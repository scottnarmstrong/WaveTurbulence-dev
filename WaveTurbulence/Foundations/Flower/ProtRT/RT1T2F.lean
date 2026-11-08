/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1T2A

/-! # RT-GATE (ii), fork C: (c−), the partner port below its window

D3's `tc_t2m_fix` (ProtPin/TChildT2mF.lean; copy recorded in RT1T-COPIED.md) with the partner (the chain tree `Xp`,
tree `0`) in the window `q' ≤ p` (`MkSlotsO.CplAmbient p q' p`: the chain tree on `timeBoxGt q' 𝔏''`, coherent with
parent layer `q'`), its lone port `𝔏'' < q'`, any piece loss `c'`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **(c−), the partner port below `p`.** -/
theorem rt1t_t2m_fix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b)
      (_hFC : TcFC P) {c' : ℝ} (_hc' : 0 ≤ c') (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGX : LayeredGarden 1}
      {LGQ LG₁ LG₂ LG₃ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
      (h : T1Data c Q₁ Q₂ Q₃ LGQ.garden LG₁.garden LG₂.garden LG₃.garden)
      (_hdQ : (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes LGQ.garden)
      (_hlA : ∀ z, LG₁.layer z = LGQ.layer (h.ιA z)) (_hlB : ∀ z, LG₂.layer z = LGQ.layer (h.ιB z))
      (_hlC : ∀ z, LG₃.layer z = LGQ.layer (h.ιC z))
      (_hwf : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).wf = true)
      (_hsz : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).size = 2 * n)
      (_hdec : (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).Decodes LG.garden) (_hle : ∀ a, LG.layer a ≤ p)
      {q' : ℕ} (_hq'p : q' ≤ p) (_hA : MkSlotsO.CplAmbient p q' p (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)) LG)
      (_hr0 : layerAt LG ((0 : Fin 2), []) ≤ q')
      (_hj : layerAt LG ((1 : Fin 2), []) = p) (_hpart : layerAt LG ((0 : Fin 2), Xp.lonePath) < q')
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
      (Hr : LeafProfiles 2 P.d) (Br : (Fin 2 × TTree.Path) → NNReal) (_hHr : LeafwiseControlled LG Hr Br)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (k : Mom P.d),
      rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LG Hr
          (gateM S ω F M Fu Mu) (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links)) *
            leafSizeProduct LG Br * starCost S cω))) * tcWt P.L k := by
  obtain ⟨Cv, hCv, hivl⟩ := tc_ivl_restr hθ0
  set Cm : ℝ≥0∞ := ENNReal.ofReal (2 ^ |θ|) * cutNormR |θ| 1 + 1 with hCm
  have hCmf : Cm < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cutNormR_lt_top _ _),
    ENNReal.one_lt_top⟩
  refine ⟨Cm * ENNReal.ofReal Cv, ENNReal.mul_lt_top hCmf ENNReal.ofReal_lt_top, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC c' hc' hC11 hθc p hp n hn LG Xp c Q₁ Q₂ Q₃ LGX LGQ LG₁ LG₂ LG₃ D h hdQ hlA hlB
    hlC hwf hsz hdec hle q' hq'p hA hr0 hj hpart s hps hsp Hr Br hHr S ω cω hpres F M hM Fu Mu hMu k
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
  have h𝔏p : (𝔏 : ℝ) + 1 ≤ q' := by exact_mod_cast hpart
  have h𝔏le : 𝔏 ≤ p := hpart.le.trans hq'p
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
  have hrX : LGX.layer (GNode.root LGX.garden.tree 0) ≤ q' := by rw [D.layX]; exact hr0
  have hloneX : ∀ a : GNode LGX.garden.tree, a.1.2 = Xp.lonePath → LGX.layer a = 𝔏 := fun a ha => by
    rw [D.layX, ha]
  -- coherence
  have hcX := rt1t_treeCoh D hdec hwX hA
  obtain ⟨w', H', a', b', hcan', hE', hsa', hsb', hlay'⟩ := rt1t_cplAmbQ D hA
  obtain ⟨hc₁, hc₂, hc₃⟩ := tc_t1_cohR h hlA hlB hlC hwQ hcan' hE' hsa' hsb' hlay'
  rw [hq0, hq1] at hc₁ hc₂ hc₃
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
  -- the identity
  set ζ : ℤˣ := LGQ.garden.sig 1 with hζ
  have hid : ∀ T : ℝ, (𝔏 : ℝ) + 1 ≤ T → kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 1 then s else T) 0 (trFix 1 s) k (fun _ => 0) 0 =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' e : T1E P.d,
        (fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 0) (t1Star c P.L k e 0) *
          fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ) *
        ∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
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
    rw [hU0, tc_t2mU_fix h𝔏.symm hT] at hid0
    exact hid0
  have hle_n : ∀ i, i ≤ n → i ≤ P.N (p + 1) ^ 4 := fun i hi => hi.trans hn
  -- the chain tree as a function of (top clock, port)
  set G : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGX (t2HX Hr) (fun _ => x 0) (x 1) k
    (fun _ => 0) 0 mX with hG
  have hGc : Continuous G := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGX (t2HX Hr) D.decX mX BX hmXB k
    (summable_coset_piece hHX hL1 k)
  have hKX : ∀ T u : ℝ, kernelProt P.L P.γ P.δ LGX (t2HX Hr) mX (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 =
      G ![T, u] := fun T u => by
    rw [cut_kernel_tree_m P.L P.γ P.δ LGX D.decX (t2HX Hr) mX T u k]
    rfl
  set bX : ℝ := P.L ^ c' * rb P nX (LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) *
    leafSizeProduct LGX (tc2BX Br) * starCost (pullS D.gd.ι₁ S) (fun z => cω (D.gd.ι₁ z)) with hbX
  have hGb : rn θ (timeBoxGt (q' : ℝ) 𝔏) G ≤ ENNReal.ofReal bX := by
    rw [hbX, ← piece_conv hL0 hrb _ _ c' nX _ _]
    exact tc_tree_mixed K hFC hp (hle_n nX (by omega)) hθc Xp LGX hwX hnX D.decX hleX (q := q') (q' := 𝔏)
      hpart.le hq'p hrX hloneX hcX _ _ _ hGX _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHX k
  have hBcl : ∀ t ∈ timeBoxGt (q' : ℝ) 𝔏, t ∈ closure (interior (timeBoxGt (q' : ℝ) 𝔏)) := fun t ht =>
    VineEstS3.timeBoxGt_subset_closure_interior (by exact_mod_cast hpart.le) ht
  have hsub : ∀ y0 ∈ Icc (q' : ℝ) (q' + 1), ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1), ![y0, u] ∈ timeBoxGt (q' : ℝ) 𝔏 := by
    intro y0 hy0 u hu
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hy0
    · simpa using (⟨hu.1.le, hu.2.le⟩ : u ∈ Icc (𝔏 : ℝ) (𝔏 + 1))
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [hu.2, hy0.1]
  have hGpt : ∀ y0 ∈ Icc (q' : ℝ) (q' + 1), ∀ u ∈ Ioo (𝔏 : ℝ) (𝔏 + 1), ‖G ![y0, u]‖ₑ ≤ ENNReal.ofReal bX :=
    fun y0 hy0 u hu => (enorm_le_rn hθ0 hBcl hGc (hsub y0 hy0 u hu)).trans hGb
  -- the sub-couples, pointwise on the mixed box
  set b₁ : ℝ := P.L ^ c' * rb P n₁ (LG₁.incoherency Q₁.links) * leafSizeProduct LG₁ (tcBA c (tc2BQ Xp Br)) *
    starCost (pullS h.ιA SQ) (fun z => cQ (h.ιA z)) with hb₁
  set b₂ : ℝ := P.L ^ c' * rb P n₂ (LG₂.incoherency Q₂.links) * leafSizeProduct LG₂ (tcBB (tc2BQ Xp Br)) *
    starCost (pullS h.ιB SQ) (fun z => cQ (h.ιB z)) with hb₂
  set b₃ : ℝ := P.L ^ c' * rb P n₃ (LG₃.incoherency Q₃.links) * leafSizeProduct LG₃ (tcBC c (tc2BQ Xp Br)) *
    starCost (pullS h.ιC SQ) (fun z => cQ (h.ιC z)) with hb₃
  set J : Mom P.d → ℝ := fun x => (jbr x ^ (30 * P.d))⁻¹ with hJ
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hJ0 : ∀ y, 0 ≤ J y := fun y => (inv_pos.2 (hjpos y)).le
  have hsI : s ∈ Icc (p : ℝ) (p + 1) := ⟨hps.le, hsp.le⟩
  have hclk : ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1), ∀ t : Fin 2,
      t1Clock 1 s u t ∈ Icc (layerAt LGQ (t, []) : ℝ) (layerAt LGQ (t, []) + 1) := by
    intro u hu t
    have hj1 : layerAt LGQ (1, []) = p := hq1
    have ho : layerAt LGQ (t1sw 1, []) = 𝔏 := hq0
    exact tc_clock_mem 1 hj1 ho hsI hu t
  have e0 : t1sw (0 : Fin 2) = 1 := by decide
  have e1 : t1sw (1 : Fin 2) = 0 := by decide
  have hrB0 : LG₂.layer (GNode.root LG₂.garden.tree 0) ≤ p := by
    have := hrB 0; rw [e0, hq1] at this; exact this
  have hrB1 : LG₂.layer (GNode.root LG₂.garden.tree 1) ≤ 𝔏 := by
    have := hrB 1; rw [e1, hq0] at this; exact this
  have hrA0 : LG₁.layer (GNode.root LG₁.garden.tree 0) ≤ 𝔏 := (hrA 0).trans hq0.le
  have hrA1 : LG₁.layer (GNode.root LG₁.garden.tree 1) ≤ p := (hrA 1).trans hq1.le
  have hrC0 : LG₃.layer (GNode.root LG₃.garden.tree 0) ≤ 𝔏 := (hrC 0).trans hq0.le
  have hrC1 : LG₃.layer (GNode.root LG₃.garden.tree 1) ≤ p := (hrC 1).trans hq1.le
  have hxA : ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1), (fun t : Fin 2 => t1Clock 1 s u t) ∈ timeBox ((𝔏 : ℕ) : ℝ) ((p : ℕ) : ℝ) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have := hclk u hu 0; rw [hq0] at this; exact this
    · have := hclk u hu 1; rw [hq1] at this; exact this
  have hxB : ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1), (fun t : Fin 2 => t1Clock 1 s u (t1sw t)) ∈
      timeBox ((p : ℕ) : ℝ) ((𝔏 : ℕ) : ℝ) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · show t1Clock 1 s u (t1sw 0) ∈ _
      rw [e0]; have := hclk u hu 1; rw [hq1] at this; exact this
    · show t1Clock 1 s u (t1sw 1) ∈ _
      rw [e1]; have := hclk u hu 0; rw [hq0] at this; exact this
  have hKA : ∀ e : T1E P.d, ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
        (k + latticePoint P.L e.1.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun t => t1Clock 1 s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₁, ← piece_conv hL0 hrb _ _ c' n₁ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₁ (by omega)) hθc Q₁ LG₁ hw₁ hn₁ h.dec₁ hle₁ h𝔏le le_rfl
      hrA0 hrA1 hc₁ _ _ _ hG₁ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₁ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) h.dec₁.1.1 m₁ B₁ hm₁B _
        (summable_coset_piece hH₁ hL1 _)) (x := fun t => t1Clock 1 s u t) (hxA u hu)
  have hKB : ∀ e : T1E P.d, ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) m₂ (fun x => t1Clock 1 s u (t1sw x.1.1)) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB (t2HQ Xp Hr)) m₂ (fun t => t1Clock 1 s u (t1sw t))]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₂, ← piece_conv hL0 hrb _ _ c' n₂ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₂ (by omega)) hθc Q₂ LG₂ hw₂ hn₂ h.dec₂ hle₂ le_rfl h𝔏le
      hrB0 hrB1 hc₂ _ _ _ hG₂ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₂ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) h.dec₂.1.1 m₂ B₂ hm₂B _
        (summable_coset_piece hH₂ hL1 _)) (x := fun t => t1Clock 1 s u (t1sw t)) (hxB u hu)
  have hKC : ∀ e : T1E P.d, ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1),
      ‖kernelProt P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
        (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0‖ₑ ≤
        ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)) := fun e u hu => by
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun t => t1Clock 1 s u t)]
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hb₃, ← piece_conv hL0 hrb _ _ c' n₃ _ _]
    exact tc_couple_pt K hFC hp (hle_n n₃ (by omega)) hθc Q₃ LG₃ hw₃ hn₃ h.dec₃ hle₃ h𝔏le le_rfl
      hrC0 hrC1 hc₃ _ _ _ hG₃ _ _ (pull_scale _ hMQs) _ _ (pull_scale _ hMuQs) _ _ hH₃ _
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) h.dec₃.1.1 m₃ B₃ hm₃B _
        (summable_coset_piece hH₃ hL1 _)) (x := fun t => t1Clock 1 s u t) (hxA u hu)
  -- continuity in the port time
  have hcA : ∀ e : T1E P.d, Continuous fun u : ℝ => kernelProt P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) m₁
      (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 := fun e => by
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) h.dec₁.1.1 m₁ B₁ hm₁B
      (k + latticePoint P.L e.1.1) (summable_coset_piece hH₁ hL1 _)
    have := hc.comp (show Continuous fun u : ℝ => (fun t : Fin 2 => t1Clock 1 s u t) by
      refine continuous_pi fun t => ?_
      fin_cases t <;> simp [t1Clock] <;> fun_prop)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply]
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₁ h.dec₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun t => t1Clock 1 s u t)]
    rfl
  have hcB : ∀ e : T1E P.d, Continuous fun u : ℝ => kernelProt P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) m₂
      (fun x => t1Clock 1 s u (t1sw x.1.1)) 0 (fun _ => none) (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 :=
    fun e => by
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) h.dec₂.1.1 m₂ B₂ hm₂B
      (k + latticePoint P.L e.1.2.1) (summable_coset_piece hH₂ hL1 _)
    have := hc.comp (show Continuous fun u : ℝ => (fun t : Fin 2 => t1Clock 1 s u (t1sw t)) by
      refine continuous_pi fun t => ?_
      fin_cases t <;> simp [t1Clock, t1sw] <;> fun_prop)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply]
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₂ h.dec₂ (t1HB (t2HQ Xp Hr)) m₂ (fun t => t1Clock 1 s u (t1sw t))]
    rfl
  have hcC : ∀ e : T1E P.d, Continuous fun u : ℝ => kernelProt P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) m₃
      (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none) (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 := fun e => by
    have hc := FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) h.dec₃.1.1 m₃ B₃ hm₃B
      (k + latticePoint P.L e.1.2.2) (summable_coset_piece hH₃ hL1 _)
    have := hc.comp (show Continuous fun u : ℝ => (fun t : Fin 2 => t1Clock 1 s u t) by
      refine continuous_pi fun t => ?_
      fin_cases t <;> simp [t1Clock] <;> fun_prop)
    refine this.congr fun u => ?_
    simp only [Function.comp_apply]
    rw [cut_kernel_couple_m P.L P.γ P.δ LG₃ h.dec₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun t => t1Clock 1 s u t)]
    rfl
  -- the weights
  set Φ : T1E P.d → ℝ → ℂ := fun e u => t1Ph ζ P.L P.γ P.δ k e s u *
    (kernelProt P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
        (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
      (kernelProt P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) m₂ (fun x => t1Clock 1 s u (t1sw x.1.1)) 0 (fun _ => none)
          (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
        kernelProt P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
          (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0)) with hΦ
  have hΦc : ∀ e, Continuous (Φ e) := fun e => by
    have hph : Continuous fun u : ℝ => t1Ph ζ P.L P.γ P.δ k e s u := by unfold t1Ph; fun_prop
    exact hph.mul ((hcA e).mul ((hcB e).mul (hcC e)))
  set Me : T1E P.d → ℝ := fun e => b₁ * b₂ * b₃ * (J (k + latticePoint P.L e.1.1) * J (k + latticePoint P.L e.1.2.1) *
    J (k + latticePoint P.L e.1.2.2)) with hMe
  have hb0 : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal),
      0 ≤ leafSizeProduct LGx Bx := fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hb10 : 0 ≤ b₁ := by
    rw [hb₁]; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hb20 : 0 ≤ b₂ := by
    rw [hb₂]; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hb30 : 0 ≤ b₃ := by
    rw [hb₃]; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hbX0 : 0 ≤ bX := by
    rw [hbX]; exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hL0 _) (hrb _ _)) (hb0 _ _)) (starCost_nonneg' _ _)
  have hMe0 : ∀ e, 0 ≤ Me e := fun e => by
    have := hJ0 (k + latticePoint P.L e.1.1); have := hJ0 (k + latticePoint P.L e.1.2.1)
    have := hJ0 (k + latticePoint P.L e.1.2.2); simp only [hMe]; positivity
  have hΦb : ∀ e, ∀ u ∈ Icc (𝔏 : ℝ) (𝔏 + 1), ‖Φ e u‖ ≤ Me e := fun e u hu => by
    have h1 : ‖Φ e u‖ₑ ≤ ENNReal.ofReal (Me e) := by
      simp only [hΦ]
      rw [enorm_mul, enorm_mul, enorm_mul, ← ofReal_norm, norm_t1Ph, ENNReal.ofReal_one, one_mul]
      calc _ ≤ (ENNReal.ofReal b₁ * ENNReal.ofReal (J (k + latticePoint P.L e.1.1))) *
            ((ENNReal.ofReal b₂ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.1))) *
              (ENNReal.ofReal b₃ * ENNReal.ofReal (J (k + latticePoint P.L e.1.2.2)))) :=
            mul_le_mul' (hKA e u hu) (mul_le_mul' (hKB e u hu) (hKC e u hu))
        _ = _ := by
            simp only [hMe]
            rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hb10 hb20) hb30), ENNReal.ofReal_mul (mul_nonneg hb10 hb20),
              ENNReal.ofReal_mul hb10, ENNReal.ofReal_mul (mul_nonneg (hJ0 _) (hJ0 _)), ENNReal.ofReal_mul (hJ0 _)]
            ring
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hMe0 e)).1 h1
  set ψ : T1E P.d → ℝ → ℂ := fun e => (Icc (𝔏 : ℝ) (𝔏 + 1)).indicator (Φ e) with hψ
  have hψm : ∀ e, Measurable (ψ e) := fun e => (hΦc e).measurable.indicator measurableSet_Icc
  have hψb : ∀ e u, ‖ψ e u‖ ≤ Me e := fun e u => by
    by_cases hu : u ∈ Icc (𝔏 : ℝ) (𝔏 + 1)
    · simp only [hψ, Set.indicator_of_mem hu]; exact hΦb e u hu
    · simp only [hψ, Set.indicator_of_notMem hu, norm_zero]; exact hMe0 e
  -- the terms
  set cc : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 with hcc
  set ae : T1E P.d → ℂ := fun e => cc * ((fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 0) (t1Star c P.L k e 0) *
    fD3' SQ ωQ FQ (fun _ => false) MQf FuQ MuQ (h.rt 1) (t1Star c P.L k e 1)) * (t1Eps c e : ℂ)) with hae
  set c2 : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hc2
  have hc20 : 0 ≤ c2 := sq_nonneg _
  have haeb : ∀ e, ‖ae e‖ₑ ≤ ENNReal.ofReal (c2 * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hae, hcc]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul (hMc _ _) (tc_abs_t1Eps_le c e) (abs_nonneg _) hCa0).trans
      (by rw [mul_one])) hc20
  set tm : T1E P.d → (Fin 1 → ℝ) → ℂ := fun e y => ae e * ∫ u in (𝔏 : ℝ)..(𝔏 + 1), ψ e u * G ![y 0, u] with htm
  have hint : ∀ e (T : ℝ), T ∈ Icc (q' : ℝ) (q' + 1) →
      (∫ u in Ioo (𝔏 : ℝ) (𝔏 + 1), t1Ph ζ P.L P.γ P.δ k e s u *
        (kernelProt P.L P.γ P.δ LGX (t2HX Hr) mX (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
          (kernelProt P.L P.γ P.δ LG₁ (t1HA c (t2HQ Xp Hr)) m₁ (fun x => t1Clock 1 s u x.1.1) 0 (fun _ => none)
              (k + latticePoint P.L e.1.1) (fun _ => 0) 0 *
            (kernelProt P.L P.γ P.δ LG₂ (t1HB (t2HQ Xp Hr)) m₂ (fun x => t1Clock 1 s u (t1sw x.1.1)) 0
                (fun _ => none) (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 *
              kernelProt P.L P.γ P.δ LG₃ (t1HC c (t2HQ Xp Hr)) m₃ (fun x => t1Clock 1 s u x.1.1) 0
                (fun _ => none) (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0)))) =
      ∫ u in (𝔏 : ℝ)..(𝔏 + 1), ψ e u * G ![T, u] := by
    intro e T _
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    have hu' : u ∈ Icc (𝔏 : ℝ) (𝔏 + 1) := ⟨hu.1.le, hu.2.le⟩
    simp only [hψ, Set.indicator_of_mem hu', hΦ, hKX]
    ring
  have hwin : ∀ y ∈ win (q' : ℝ), kernelProt P.L P.γ P.δ LG Hr (gateM S ω F M Fu Mu)
      (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k (fun _ => 0) 0 = ∑' e, tm e y := by
    intro y hy
    rw [hid (y 0) (h𝔏p.trans hy.1), ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    simp only [htm, hae]
    rw [hint e (y 0) hy]
    ring
  -- the bound of one term
  have htmb : ∀ e, rn θ (win (q' : ℝ)) (tm e) ≤
      ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal Cv * ENNReal.ofReal (Me e) * ENNReal.ofReal bX) := fun e => by
    refine (tc_rn_mul_le θ _ (ae e) _).trans (mul_le_mul' (haeb e) ?_)
    exact (hivl (ψ e) (Me e) (hψm e) (hψb e) q' 𝔏 _ hBcl hsub G hGc).trans (mul_le_mul' le_rfl hGb)
  -- summability on the window
  have hMsum : ∑' e, ENNReal.ofReal (Me e) ≤ ENNReal.ofReal (b₁ * b₂ * b₃) * tcWt P.L k := by
    have he : ∀ e : T1E P.d, ENNReal.ofReal (Me e) = ENNReal.ofReal (b₁ * b₂ * b₃) *
        (tcJ (k + latticePoint P.L e.1.1) * tcJ (k + latticePoint P.L e.1.2.1) * tcJ (k + latticePoint P.L e.1.2.2)) :=
      fun e => by
      simp only [hMe, tcJ, hJ]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hb10 hb20) hb30),
        ENNReal.ofReal_mul (mul_nonneg (inv_pos.2 (hjpos _)).le (inv_pos.2 (hjpos _)).le),
        ENNReal.ofReal_mul (inv_pos.2 (hjpos _)).le]
    simp_rw [he]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl le_self_add
  have hWfin : ENNReal.ofReal (b₁ * b₂ * b₃) * tcWt P.L k < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tc_tcWt_lt_top hd1 hL1 k)
  have hsum : ∀ y ∈ win (q' : ℝ), Summable fun e => tm e y := by
    intro y hy
    have hb : ∀ e, ‖tm e y‖ₑ ≤ ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal (Me e) * ENNReal.ofReal bX) := by
      intro e
      simp only [htm]
      rw [enorm_mul, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      refine mul_le_mul' (haeb e) ((enorm_integral_le_lintegral_enorm _).trans ?_)
      refine (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (Me e) * ENNReal.ofReal bX) measurableSet_Ioo
        fun u hu => ?_).trans (le_of_eq ?_)
      · rw [enorm_mul]
        refine mul_le_mul' ?_ (hGpt (y 0) hy u hu)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hψb e u)
      · rw [setLIntegral_const, Real.volume_Ioo, show (𝔏 : ℝ) + 1 - 𝔏 = 1 by ring, ENNReal.ofReal_one, mul_one]
    have hfin : ∑' e, ‖tm e y‖ₑ ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hMsum.trans_lt hWfin).ne)
        ENNReal.ofReal_ne_top
    refine Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)
    simpa only [enorm_eq_nnnorm] using hfin
  -- Minkowski over the exceptional data
  rw [rn_congr θ hwin]
  have hBc : win (q' : ℝ) ⊆ VineEstS3.FS.cell (fun _ : Fin 1 => (q' : ℝ)) := fun y hy i => by
    rw [Subsingleton.elim i 0]; exact hy
  letI : MeasurableSpace (T1E P.d) := ⊤
  haveI : MeasurableSingletonClass (T1E P.d) := ⟨fun _ => trivial⟩
  have hMk := VineEstS3.Mink.XNorm00Restr_tsum_le (ι := T1E P.d) hθ0 (fun _ : Fin 1 => (q' : ℝ)) hBc
    Set.countable_univ (fun e t (_ : Unit) => tm e t) (fun t _ => ∑' e, tm e t) (fun t ht _ _ => (hsum t ht).hasSum)
  rw [tc_cmc_eq] at hMk
  refine (show rn θ (win (q' : ℝ)) (fun y => ∑' e, tm e y) ≤ Cm * ∑' e, rn θ (win (q' : ℝ)) (tm e) from hMk).trans ?_
  calc Cm * ∑' e, rn θ (win (q' : ℝ)) (tm e)
      ≤ Cm * ∑' e, ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal Cv * ENNReal.ofReal (Me e) * ENNReal.ofReal bX) :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum htmb)
    _ = Cm * ENNReal.ofReal Cv * (ENNReal.ofReal (c2 * Ca) * ENNReal.ofReal bX * ∑' e, ENNReal.ofReal (Me e)) := by
        have hre : ∀ e, ENNReal.ofReal (c2 * Ca) * (ENNReal.ofReal Cv * ENNReal.ofReal (Me e) * ENNReal.ofReal bX) =
            (ENNReal.ofReal Cv * (ENNReal.ofReal (c2 * Ca) * ENNReal.ofReal bX)) * ENNReal.ofReal (Me e) :=
          fun e => by ring
        simp_rw [hre]
        rw [ENNReal.tsum_mul_left]
        ring
    _ ≤ Cm * ENNReal.ofReal Cv * (ENNReal.ofReal (c2 * Ca) * ENNReal.ofReal bX *
          (ENNReal.ofReal (b₁ * b₂ * b₃) * tcWt P.L k)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hMsum)
    _ ≤ _ := by
        -- the algebra
        have hg2 := tc2_incoh D hdec hdQ
        have hgQ := tc_t1_incoh h hlA hlB hlC
        rw [hq0, hq1, if_neg (by omega)] at hgQ
        set g := LG.incoherency (RegCpl.type2 Xp .nil (.type1 c Q₁ Q₂ Q₃)).links with hgdef
        have hn1 : nX + n₁ + n₂ + n₃ = n - 1 := by omega
        have hleaf : leafSizeProduct LG Br = leafSizeProduct LGX (tc2BX Br) * (leafSizeProduct LG₁ (tcBA c (tc2BQ Xp Br)) *
            leafSizeProduct LG₂ (tcBB (tc2BQ Xp Br)) * leafSizeProduct LG₃ (tcBC c (tc2BQ Xp Br))) := by
          rw [tc2_leafSize D Br, tc_t1_leafSize h (tc2BQ Xp Br)]
        have hcost : starCost S cω = starCost (pullS D.gd.ι₁ S) (fun z => cω (D.gd.ι₁ z)) *
            (Ca * (starCost (pullS h.ιA SQ) (fun z => cQ (h.ιA z)) * (starCost (pullS h.ιB SQ) (fun z => cQ (h.ιB z)) *
              starCost (pullS h.ιC SQ) (fun z => cQ (h.ιC z))))) := by
          rw [tc2_cost D hr S cω, tc_t1_cost h SQ cQ]
        have hval : c2 * Ca * bX * (b₁ * b₂ * b₃) =
            P.L ^ (4 * c') * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (g - 1)) * leafSizeProduct LG Br *
              starCost S cω) := by
          have hgg : g - 1 = LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0)) + LG₁.incoherency Q₁.links +
              LG₂.incoherency Q₂.links + LG₃.incoherency Q₃.links := by rw [hg2, hgQ]; omega
          have h4 := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := nX) (n₂ := n₁) (n₃ := n₂) (n₄ := n₃)
            (g₁ := LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) (g₂ := LG₁.incoherency Q₁.links)
            (g₃ := LG₂.incoherency Q₂.links) (g₄ := LG₃.incoherency Q₃.links)
          have h4' : rb P nX (LGX.incoherency (Xp.treeLinks (LGX.garden.sig 0))) * rb P n₁ (LG₁.incoherency Q₁.links) *
              rb P n₂ (LG₂.incoherency Q₂.links) * rb P n₃ (LG₃.incoherency Q₃.links) =
              P.C₁ ^ 3 * rb P (n - 1) (g - 1) := by
            rw [h4, ← hn1, hgg]; rfl
          rw [hbX, hb₁, hb₂, hb₃, hleaf, hcost, hc2, ← h4', ← rt1t_rpow4 (by linarith : (0 : ℝ) < P.L) c']
          ring
        have hpred := rb_pred_le hL1 hC1 K.hδ K.hη0 (n - 1) (show 1 ≤ g by rw [hg2, hgQ]; omega)
        rw [Real.rpow_one] at hpred
        have hY : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω := by
          have := starCost_nonneg' S cω
          have := hb0 LG Br
          positivity
        have hfin : coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (g - 1)) * leafSizeProduct LG Br *
            starCost S cω ≤ P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) g) *
              leafSizeProduct LG Br * starCost S cω) :=
          calc coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (g - 1)) * leafSizeProduct LG Br * starCost S cω
              = (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) *
                  rb P (n - 1) (g - 1) := by ring
            _ ≤ (coupling P.d P.L P.γ P.δ ^ 2 * P.C₁ ^ 3 * leafSizeProduct LG Br * starCost S cω) *
                  (P.L * rb P (n - 1) g) := mul_le_mul_of_nonneg_left hpred hY
            _ = _ := by ring
        have hprod : ENNReal.ofReal (c2 * Ca) * ENNReal.ofReal bX * (ENNReal.ofReal (b₁ * b₂ * b₃) * tcWt P.L k) =
            ENNReal.ofReal (c2 * Ca * bX * (b₁ * b₂ * b₃)) * tcWt P.L k := by
          rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc20 hCa0) hbX0), ENNReal.ofReal_mul (mul_nonneg hc20 hCa0)]
          ring
        rw [hprod, hval]
        calc Cm * ENNReal.ofReal Cv * (ENNReal.ofReal (P.L ^ (4 * c') * (coupling P.d P.L P.γ P.δ ^ 2 *
              (P.C₁ ^ 3 * rb P (n - 1) (g - 1)) * leafSizeProduct LG Br * starCost S cω)) * tcWt P.L k)
            ≤ Cm * ENNReal.ofReal Cv * (ENNReal.ofReal (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
                (P.C₁ ^ 3 * rb P (n - 1) g) * leafSizeProduct LG Br * starCost S cω))) * tcWt P.L k) :=
              mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left hfin (Real.rpow_nonneg (by linarith) _))) le_rfl)
          _ = _ := by ring

end WaveTurbulence.Flower.ProtRT
