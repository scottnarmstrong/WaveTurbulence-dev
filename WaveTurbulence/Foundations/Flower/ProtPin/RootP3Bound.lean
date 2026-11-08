/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootRest
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo
public import WaveTurbulence.Foundations.Flower.ProtPin.PenCont
public import WaveTurbulence.Foundations.Flower.ProtPin.PenSub
public import WaveTurbulence.Foundations.Flower.ProtPin.Pen5
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckP3

/-! # D3 PROT-PIN: (P3) — root at `t`, terminal node in the suffix at `s` (`rest ≠ nil`), in `X^{θ,30d,0}`

D2c's `kernelProt_rootTerm_cfg3`: on the R176 box the kernel is the constant
`Σ'_e c_e ∫_{Ioo s t} e^{πiA_e(t-u)} K₃(u) W_e(t, u) du`, where `K₃(u)` is the suffix (code `rest`) with its terminal
node pinned at `s` and the dagger `indS` (a `term` object, `RootData.termChild_indS`), its port clock irrelevant
(`kernelProt_port_term`). Pointwise: `|K₃(u)| ≤ rn(K₃)` (continuity in the upper clock, `pen_continuous_kernelProt_up`),
bounded by the `term` per-output bound of the suffix as a protected sub-object (`TermStarPerkU`, `starMult_tree`); the
closing pair as in `root_pack`. Two cuts: `twoRb`, `final_two`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem rootU3_eq {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {s t T : ℝ} (hps : (p : ℝ) < s) (htp : t < p + 1)
    (hT : t ≤ T) : rootU3 LG m inner T t s = Ioo s t := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU3, rootU, hlay, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨-, -, -, -, h5⟩, h6⟩
    exact ⟨h6, h5⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, by linarith, by linarith, by linarith, h2⟩, h1⟩

theorem term_fix_up (X : RegChain) (s t u u' : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.term.fix X s t u : GBranch T → Option ℝ) = ProtCfg.term.fix X s t u' := rfl

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain}

/-- **(P3), one output** (stars, filters, dagger; R176 box). -/
theorem p3_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
      {inner rest : RegChain} (_D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
      (_hsh : ProtShape p (RegChain.pair m Qr Qg inner rest) LG)
      (_hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
      (_hamb : TreeAmb p (RegChain.pair m Qr Qg inner rest) LG) {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t)
      (_htp : t < p + 1) (q' : ℕ)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
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
        C * ENNReal.ofReal (twoRb P (7 * c') n (protIncoh (RegChain.pair m Qr Qg inner rest) LG)
          (leafSizeProduct LG B) (starCost S cω)) := by
  obtain ⟨Ct, hCt0, hperkT⟩ := exists_termStarPerkU hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨cutNormR θ 2 * T4 * ENNReal.ofReal Ct, ENNReal.mul_lt_top (ENNReal.mul_lt_top (cutNormR_lt_top θ 2)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGZ LGi LGs LGr LGg m Qr Qg inner rest D hsh hsz hamb s t hps hst
    htp q' H B hH S ω cω hpres F M hM Fu Mu hMu ind hind k
  obtain ⟨hwfs, hwfi, hwfr, hwfg⟩ := root_wf hsh.1
  obtain ⟨ns, ni, nr, ng, hns, hni, hnr, hng, hnsum⟩ := root_sizes hsz
  obtain ⟨hshS, hli, hlonei, hlr, hlg⟩ := root_layers D hsh
  obtain ⟨hHs, hHi, hHr, hHg⟩ := root_leafwise D hH
  obtain ⟨hambS, fI, fR, fG⟩ := root_flat D hsh hamb
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  have hns1 : 1 ≤ ns := by have := pen_size_two rest D.rest_lonePath_ne; omega
  set ζ := LG.garden.sig 0 with hζ
  -- the multiplier: closing pair in gate form, dagger in the suffix
  have hX : RegChain.pair m Qr Qg inner rest ≠ .nil := by simp
  have hMf0 := D.multFactors_D3 S ω F (fun _ => false) M Fu Mu ind hind
  set βs : GBranch LGs.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inr y) with hβs
  set βi : GBranch LGi.garden.tree → GBranch LG.garden.tree := fun x => D.gd.ofSum (.inl (D.hp.βi x)) with hβi
  set βr : GBranch LGr.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inl (D.hp.βr y)) with hβr
  set βg : GBranch LGg.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inl (D.hp.βg y)) with hβg
  set ms := pullMult D.ιS βs S ω F M Fu Mu with hms
  set mi := pullMult D.ιI βi S ω F M Fu Mu with hmi
  set mr := pullMult D.ιR βr S ω F M Fu Mu with hmr
  set mg := pullMult D.ιG βg S ω F M Fu Mu with hmg
  set m3 : (GNode LGs.garden.tree → Mom P.d) → ℂ := fun K => ms K * (indS m inner ind K : ℂ) with hm3
  have hMf : D.MultFactors
      (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3' S ω F (fun _ => false) M Fu Mu D.aR A * fD3' S ω F (fun _ => false) M Fu Mu D.bR B)
      mi mr mg m3 := by
    intro K
    rw [hMf0 K]
    simp only [hmi, hmr, hmg, hm3, hms, pullMult, βi, βr, βg, βs]
    rw [pull_mult (rootEmbI D), pull_mult (rootEmbR D), pull_mult (rootEmbG D), pull_mult (rootEmbS D)]
  have hMc := star_root_Mc_le D S ω cω hpres F M Fu Mu
  have hGs := pull_pres (J := 30 * P.d) D.ιS hpres
  have hGi := pull_pres (J := 30 * P.d) D.ιI hpres
  have hGr := pull_pres (J := 30 * P.d) D.ιR hpres
  have hGg := pull_pres (J := 30 * P.d) D.ιG hpres
  have hmsB := FiltCoh.norm_d5Mult_le (pullS D.ιS S) (fun z => ω (D.ιS z)) (fun z => cω (D.ιS z)) hGs
    (pullF βs F) (fun _ => false) (fun y => M (βs y)) (pullF βs Fu) (fun y => Mu (βs y))
  have hmiB := FiltCoh.norm_d5Mult_le (pullS D.ιI S) (fun z => ω (D.ιI z)) (fun z => cω (D.ιI z)) hGi
    (pullF βi F) (fun _ => false) (fun y => M (βi y)) (pullF βi Fu) (fun y => Mu (βi y))
  have hmrB := FiltCoh.norm_d5Mult_le (pullS D.ιR S) (fun z => ω (D.ιR z)) (fun z => cω (D.ιR z)) hGr
    (pullF βr F) (fun _ => false) (fun y => M (βr y)) (pullF βr Fu) (fun y => Mu (βr y))
  have hmgB := FiltCoh.norm_d5Mult_le (pullS D.ιG S) (fun z => ω (D.ιG z)) (fun z => cω (D.ιG z)) hGg
    (pullF βg F) (fun _ => false) (fun y => M (βg y)) (pullF βg Fu) (fun y => Mu (βg y))
  set Ca : ℝ := costB S cω D.aR * costB S cω D.bR with hCa
  have hCa0 : 0 ≤ Ca := mul_nonneg (costB_nonneg _ _ _) (costB_nonneg _ _ _)
  set Bs : ℝ := (∏ a ∈ pullS D.ιS S, max (cω (D.ιS a)) 0) * FiltCoh.chiDSup ^ (pullF βs F).card *
    FiltCoh.chiDSup ^ (pullF βs Fu).card with hBs
  set Bi : ℝ := (∏ a ∈ pullS D.ιI S, max (cω (D.ιI a)) 0) * FiltCoh.chiDSup ^ (pullF βi F).card *
    FiltCoh.chiDSup ^ (pullF βi Fu).card with hBi
  set Br : ℝ := (∏ a ∈ pullS D.ιR S, max (cω (D.ιR a)) 0) * FiltCoh.chiDSup ^ (pullF βr F).card *
    FiltCoh.chiDSup ^ (pullF βr Fu).card with hBr
  set Bg : ℝ := (∏ a ∈ pullS D.ιG S, max (cω (D.ιG a)) 0) * FiltCoh.chiDSup ^ (pullF βg F).card *
    FiltCoh.chiDSup ^ (pullF βg Fu).card with hBg
  set CM : ℝ := max Ca (max Bs (max Bi (max Br Bg))) with hCM
  have hind3 : TermChildIndicator rest (indS m inner ind : (GNode LGs.garden.tree → Mom P.d) → ℝ) :=
    D.termChild_indS ind hind
  have hm3B : ∀ K, ‖m3 K‖ ≤ Bs := fun K => by
    rw [hm3, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hind3.1 K).1]
    calc ‖ms K‖ * indS m inner ind K ≤ Bs * 1 :=
          mul_le_mul (hmsB K) (hind3.1 K).2 (hind3.1 K).1 ((norm_nonneg _).trans (hmsB K))
      _ = Bs := mul_one _
  -- the suffix: a `term` object
  set K3 : (Fin 2 → ℝ) → ℂ := fun x => kernelProt P.L P.γ P.δ LGs (rootHs m inner H) m3 (fun _ => x 0) (x 1)
    (ProtCfg.term.fix rest s t (x 0)) k (fun _ => 0) 0 with hK3
  have hK3port : ∀ x : Fin 2 → ℝ, K3 x = kernelProt P.L P.γ P.δ LGs (rootHs m inner H) m3 (fun _ => x 0) s
      (ProtCfg.term.fix rest s t 0) k (fun _ => 0) 0 := fun x => by
    simp only [hK3]
    rw [term_fix_up rest s t (x 0) 0]
    exact kernelProt_port_term P.L P.γ P.δ D.decS (rootHs m inner H) m3 (fun _ => x 0) (x 1) s s t 0 k
  have hK3c : Continuous K3 := by
    rw [show K3 = fun x : Fin 2 → ℝ => kernelProt P.L P.γ P.δ LGs (rootHs m inner H) m3 (fun _ => x 0) s
      (ProtCfg.term.fix rest s t 0) k (fun _ => 0) 0 from funext hK3port]
    exact (pen_continuous_kernelProt_up P.L P.γ P.δ LGs (rootHs m inner H) m3 Bs hm3B s _ k
      (card_lone_le_of_decodesTree D.decS) (summable_coset_piece hHs hL1 k)).comp (continuous_apply 0)
  have hCSs := starCost_nonneg' (pullS D.ιS S) (fun z => cω (D.ιS z))
  have hSM : StarMult P.L LGs rest m3 (starCost (pullS D.ιS S) (fun z => cω (D.ιS z))) :=
    starMult_tree (L := P.L) (X := rest) (pullS D.ιS S) (fun z => ω (D.ιS z)) (fun z => cω (D.ιS z)) hGs
      (pullF βs F) (fun y => M (βs y)) (pull_scale _ hM) (pullF βs Fu) (fun y => Mu (βs y)) (pull_scale _ hMu)
      (indS m inner ind) hind3
  set gs := LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) with hgs
  have hK3b : rn θ (timeBoxGt p p) K3 ≤ ENNReal.ofReal (Ct * termRb P c' ns gs
      (leafSizeProduct LGs (rootBs m inner B)) (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)))) :=
    hperkT K hθc hp (hle_n ns (by omega)) LGs rest hshS hns hambS D.rest_lonePath_ne hps (hst.trans htp) t p
      (rootHs m inner H) (rootBs m inner B) hHs m3 _ hSM k
  -- the closing pair
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGi
    (cutHi .nil m H) (fun _ => x 0) (x 1) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 mi with hKi
  set fr : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGr
    (cutHr .nil m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 mr
    with hfr
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg .nil m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fr e (cupR m inner ζ (x 0) (x 1) 0) (cupR m inner ζ (x 0) (x 1) 1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Ki e x * (Kr e x * Kg e x) with hW
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi .nil m H) D.decI mi Bi hmiB _
      (summable_coset_piece hHi hL1 _)
  have hor : ∀ {f : ℝ → ℝ → ℂ} (c : ℝ → ℝ → Fin 2 → ℝ),
      ((∀ u v, c u v 0 = u ∧ c u v 1 = v) ∨ (∀ u v, c u v 0 = v ∧ c u v 1 = u)) →
      Continuous (fun x : Fin 2 → ℝ => f (x 0) (x 1)) →
      Continuous (fun x : Fin 2 → ℝ => f (c (x 0) (x 1) 0) (c (x 0) (x 1) 1)) := by
    intro f c hc hf
    rcases hc with hc | hc
    · simpa only [(hc _ _).1, (hc _ _).2] using hf
    · simp only [(hc _ _).1, (hc _ _).2]
      exact hf.comp (show Continuous fun x : Fin 2 → ℝ => ![x 1, x 0] by fun_prop)
  have hKrc : ∀ e, Continuous (Kr e) := fun e =>
    hor (f := fr e) (cupR m inner ζ) (cupR_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr .nil m inner ζ H) D.decR.1.1 mr Br hmrB _
        (summable_coset_piece hHr hL1 _))
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fg e) (cupG m inner ζ) (cupG_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg .nil m inner ζ H) D.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hWc : ∀ e, Continuous (W e) := fun e => (hKic e).mul ((hKrc e).mul (hKgc e))
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set bi : ℝ := P.L ^ c' * rb P ni gi * leafSizeProduct LGi (cutBi .nil m B) *
    starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) with hbi
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
    starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg .nil m inner ζ B) *
    starCost (pullS D.ιG S) (fun z => cω (D.ιG z)) with hbg
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← piece_conv hL0 hrb _ _ c' ni gi _]
    exact tree_piece_star K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni D.decI hli hlonei fI _ _ _ hGi
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) (cutHi .nil m H) (cutBi .nil m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fr e) (cupR m inner ζ) (cupR_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb _ _ c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR hlr fR _ _ _ hGr
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb _ _ c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG _ _ _ hGg
      _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt p p) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfini : ∀ e, rn θ (timeBoxGt p p) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kr e) * rn θ (timeBoxGt p p) (Kg e) := fun e =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt p p) (W e) ≤
      T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Ki e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfini e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Ki e) * rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bi *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKib e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  -- the identity on the R176 box: a constant
  have hHsum : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
    fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)) with hc
  have hMc' := fun A B => (hMc A B).trans (le_max_left Ca (max Bs (max Bi (max Br Bg))))
  have hms' := fun κ => (hm3B κ).trans ((le_max_left _ _).trans (le_max_right Ca (max Bs (max Bi (max Br Bg)))))
  have hmi' := fun κ => (hmiB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg))))))
  have hmr' := fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg)))))))
  have hmg' := fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg)))))))
  have hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p := by
    rw [← D.layer_bR]
    have hbp : D.bR.1.2 = bPath m inner := congrArg Prod.snd D.bR_path
    refine hsh.2.2.2 D.bR (Nat.lt_one_iff.mp D.bR.1.1.isLt) ?_ ?_
    · rw [hbp, root_lonePath]; exact List.prefix_append _ _
    · rw [hbp, root_lonePath]; simp
  set V : ℂ := ∑' e, c e * ∫ u in Ioo s t, rootPh (A e) t u * (K3 ![u, p] * W e ![t, u]) with hV
  have hcfg : ∀ ts ∈ ProtCfg.rootTerm.box (RegChain.pair m Qr Qg inner rest) t p q',
      kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.rootTerm.fix (RegChain.pair m Qr Qg inner rest) s t (ts 0)) k
          (fun _ => 0) 0 = V := by
    intro ts hts
    rw [box_rootTerm] at hts
    rw [kernelProt_rootTerm_cfg3 D P.L P.γ P.δ H hHsum _ _ _ _ _ _ hMf CM hMc' hmi' hmr' hmg' hms' (ts 0) (ts 1) s t
      hts.2 k, rootU3_eq hlay hps htp hts.2, hV, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
      fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [hK3port ![u, p]]
    simp only [Matrix.cons_val_zero, cut_kernel_tree_m _ _ _ _ D.decI, cut_kernel_couple_m _ _ _ _ D.decR,
      cut_kernel_couple_m _ _ _ _ D.decG]
    rw [kernelProt_port_term P.L P.γ P.δ D.decS (rootHs m inner H) m3 (fun _ => u) (ts 1) s s t u k,
      term_fix_up rest s t u 0]
    rfl
  rw [rn_congr θ hcfg, box_rootTerm]
  refine (rn_const_le θ ![(p : ℝ), (q' : ℝ)] (rootBox_sub_cell (p : ℝ) q' t) V).trans ?_
  -- the pointwise bound
  have hVb : ‖V‖ₑ ≤ rn θ (timeBoxGt p p) K3 * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) := by
    rw [hV, ← ENNReal.tsum_mul_left]
    refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun e => ?_)
    rw [enorm_mul, mul_left_comm]
    refine mul_le_mul' le_rfl ((enorm_integral_le_lintegral_enorm _).trans ?_)
    have hpt' : ∀ u ∈ Ioo s t, ‖rootPh (A e) t u * (K3 ![u, p] * W e ![t, u])‖ₑ ≤
        rn θ (timeBoxGt p p) K3 * rn θ (timeBoxGt p p) (W e) := by
      intro u hu
      rw [enorm_mul, ← ofReal_norm, norm_rootPh, ENNReal.ofReal_one, one_mul, enorm_mul]
      have hm1 : (![u, (p : ℝ)] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) p := by
        refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
      have hm2 : (![t, u] : Fin 2 → ℝ) ∈ timeBoxGt (p : ℝ) p := by
        refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith [hu.1, hu.2]
      exact mul_le_mul' (enorm_le_rn hθ0 (timeBoxGt_cl p) hK3c hm1) (enorm_le_rn hθ0 (timeBoxGt_cl p) (hWc e) hm2)
    calc ∫⁻ u in Ioo s t, ‖rootPh (A e) t u * (K3 ![u, p] * W e ![t, u])‖ₑ
        ≤ ∫⁻ _ in Ioo s t, rn θ (timeBoxGt p p) K3 * rn θ (timeBoxGt p p) (W e) :=
          setLIntegral_mono' measurableSet_Ioo hpt'
      _ = rn θ (timeBoxGt p p) K3 * rn θ (timeBoxGt p p) (W e) * volume (Ioo s t) := setLIntegral_const _ _
      _ ≤ rn θ (timeBoxGt p p) K3 * rn θ (timeBoxGt p p) (W e) * 1 := by
          refine mul_le_mul' le_rfl ?_
          rw [Real.volume_Ioo, ENNReal.ofReal_le_one]
          linarith
      _ = _ := mul_one _
  -- the exceptional sum
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  have hcc0 : 0 ≤ cc := sq_nonneg _
  have hc0n : ‖c₀‖ = cc := norm_cutPrefactor hL0 K.hδ _ _
  have hce : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal (cc * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hMe : ‖(fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
        fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)‖ ≤ Ca := by
      refine (norm_mul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa0).trans (by rw [mul_one])
    calc ‖c e‖ = ‖c₀‖ * ‖(fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
        fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)‖ := norm_mul _ _
      _ ≤ cc * Ca := by rw [hc0n]; exact mul_le_mul_of_nonneg_left hMe hcc0
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  set Z : ℝ≥0∞ := ENNReal.ofReal (cc * Ca) * T4 * (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg)
    with hZ
  have hterm : ∀ e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) ≤ Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
    calc ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e)
        ≤ ENNReal.ofReal (cc * Ca) * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
            ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))))) :=
          mul_le_mul' (hce e) (hWb e)
      _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
  have hsum : ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt p p) (W e) ≤
      Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
      exact tsum_decay_le hd1 hL1 k
  refine (mul_le_mul' (hVb.trans (mul_le_mul' hK3b hsum)) le_rfl).trans ?_
  -- the algebra
  have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hn2 : (ns - 1) + ni + nr + ng = n - 2 := by omega
  have hg : gs + gi + gr + gg = protIncoh (RegChain.pair m Qr Qg inner rest) LG :=
    (D.incoherency_rootCut_of_chainIn hsh.2.2.2).symm
  have hleaf : leafSizeProduct LG B = leafSizeProduct LGs (rootBs m inner B) *
      leafSizeProduct LGi (cutBi .nil m B) * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
        leafSizeProduct LGg (cutBg .nil m inner ζ B) := by
    rw [root_leafSize D B]; ring
  have hcost : starCost S cω = Ca * (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) *
      (starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) * (starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) *
        starCost (pullS D.ιG S) (fun z => cω (D.ιG z))))) := by
    unfold starCost
    rw [star_root_cost D S cω]
  have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := ns - 1) (n₂ := ni) (n₃ := nr) (n₄ := ng)
    (g₁ := gs) (g₂ := gi) (g₃ := gr) (g₄ := gg)
  have hrbe : rb P (n - 2) (protIncoh (RegChain.pair m Qr Qg inner rest) LG) =
      P.C₁ * (P.C₁ * P.δ) ^ (ns - 1 + ni + nr + ng) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((gs + gi + gr + gg : ℕ) : ℝ)) := by
    rw [← hn2, ← hg]; rfl
  have h7 : P.L ^ (7 * c') = P.L ^ (4 * c') * P.L ^ c' * P.L ^ c' * P.L ^ c' := by
    rw [show 7 * c' = 4 * c' + c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
  have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
  have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa0
  have hts0 : 0 ≤ termRb P c' ns gs (leafSizeProduct LGs (rootBs m inner B))
      (starCost (pullS D.ιS S) (fun z => cω (D.ιS z))) :=
    termRb_nonneg hC1 K.hδ hL0 _ _ (hls _ _) hCSs
  have hval : Ct * termRb P c' ns gs (leafSizeProduct LGs (rootBs m inner B))
        (starCost (pullS D.ιS S) (fun z => cω (D.ιS z))) *
      (cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))) =
      Ct * twoRb P (7 * c') n (protIncoh (RegChain.pair m Qr Qg inner rest) LG) (leafSizeProduct LG B)
        (starCost S cω) := by
    rw [termRb, twoRb, hcost, hleaf, hrbe, h7, hbi, hbr, hbg]
    have e3 : rb P (ns - 1) gs * rb P ni gi * rb P nr gr * rb P ng gg =
        P.C₁ ^ 3 * (P.C₁ * (P.C₁ * P.δ) ^ (ns - 1 + ni + nr + ng) *
          P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((gs + gi + gr + gg : ℕ) : ℝ))) := h4r
    linear_combination (Ct * cc * Ca * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) *
      (latC P.d * P.L ^ P.d) ^ 2 * P.L ^ (4 * c') * P.L ^ c' * P.L ^ c' * P.L ^ c' * P.C₁ ^ 3 *
      leafSizeProduct LGs (rootBs m inner B) * starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) *
      leafSizeProduct LGi (cutBi .nil m B) * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
      leafSizeProduct LGg (cutBg .nil m inner ζ B) * starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) *
      starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) * starCost (pullS D.ιG S) (fun z => cω (D.ιG z))) * e3
  rw [hZ, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul (mul_nonneg hi0 hr0), ← ENNReal.ofReal_mul hlat0]
  calc ENNReal.ofReal (Ct * termRb P c' ns gs (leafSizeProduct LGs (rootBs m inner B))
          (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)))) *
        (ENNReal.ofReal (cc * Ca) * T4 * ENNReal.ofReal (bi * br * bg) *
          ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))) * cutNormR θ 2
      = cutNormR θ 2 * T4 * (ENNReal.ofReal (Ct * termRb P c' ns gs (leafSizeProduct LGs (rootBs m inner B))
          (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)))) * (ENNReal.ofReal (cc * Ca) *
            ENNReal.ofReal (bi * br * bg) * ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)))) := by
        ring
    _ = cutNormR θ 2 * T4 * ENNReal.ofReal (Ct * termRb P c' ns gs (leafSizeProduct LGs (rootBs m inner B))
          (starCost (pullS D.ιS S) (fun z => cω (D.ιS z))) *
          (cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)))) := by
        rw [← ENNReal.ofReal_mul hccCa,
          ← ENNReal.ofReal_mul (mul_nonneg hccCa (mul_nonneg (mul_nonneg hi0 hr0) hg0)),
          ← ENNReal.ofReal_mul (mul_nonneg hCt0 hts0)]
    _ = cutNormR θ 2 * T4 * ENNReal.ofReal (Ct * twoRb P (7 * c') n
          (protIncoh (RegChain.pair m Qr Qg inner rest) LG) (leafSizeProduct LG B) (starCost S cω)) := by
        rw [hval]
    _ ≤ _ := by
        rw [ENNReal.ofReal_mul hCt0]
        exact le_of_eq (by ring)

end WaveTurbulence.Flower.ProtPin
