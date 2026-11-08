/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.TreePack

/-! # RT-GATE (i): the root-cut package with a suffix, multi-layer (`rt_root_pack`)

D3's `root_pack` (ProtPin/RootPack.lean; copy recorded in COPIED-SHA256SUMS) for a paired tree
`X = pair m Qr Qg inner rest` (`rest ≠ nil`) whose chain need not lie in one layer: root layer `ℓ₀`, closing node `𝔫_b`
in layer `ℓb ≤ ℓ₀`, lone leaf in layer `q' ≤ ℓb`. Given the eligibility of the pieces (`RtElig`), at one output: the
coefficients `c e`, frequencies `A e`, closing-pair products `W e` (finite norms on `timeBoxGt ℓ₀ ℓb`), the suffix `Ks`
(finite norm on `timeBoxGt ℓb q'`, vanishing below the port), the exceptional sum
`rn(Ks) · Σ'_e ‖c e‖ rn(W e) ≤ 4^θ · termRb(g')` with `g'` the sum of the pieces' incoherencies, and D2c's identity. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **Eligibility of the closing-pair pieces** of a root cut for the mixed-layer gates: windows `ℓ₀` (the root) and
`ℓb` (the closing node), layers, root and lone layers, and coherence in the ambient. -/
structure RtEligP (p ℓ₀ ℓb : ℕ) (ζ : ℤˣ) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain)
    (LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2) : Prop where
  hℓb : ℓb ≤ ℓ₀
  hℓ₀ : ℓ₀ ≤ p
  leI : ∀ a, LGi.layer a ≤ p
  rI : LGi.layer (GNode.root LGi.garden.tree 0) ≤ ℓ₀
  loneI : ∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath → LGi.layer a = ℓb
  cohI : LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) = 0 → IsCoherentTreeAt p ℓ₀ ℓb inner LGi
  leR : ∀ a, LGr.layer a ≤ p
  rR : ∀ t, LGr.layer (GNode.root LGr.garden.tree t) ≤ tc2aQR m inner ζ ℓ₀ ℓb t
  cohR : LGr.incoherency Qr.links = 0 →
    IsCoherentCoupleAt p (tc2aQR m inner ζ ℓ₀ ℓb 0) (tc2aQR m inner ζ ℓ₀ ℓb 1) Qr LGr
  leG : ∀ a, LGg.layer a ≤ p
  rG : ∀ t, LGg.layer (GNode.root LGg.garden.tree t) ≤ tc2aQG m inner ζ ℓ₀ ℓb t
  cohG : LGg.incoherency Qg.links = 0 →
    IsCoherentCoupleAt p (tc2aQG m inner ζ ℓ₀ ℓb 0) (tc2aQG m inner ζ ℓ₀ ℓb 1) Qg LGg

/-- **Eligibility of the suffix** (window `ℓb`, port layer `q'`). -/
structure RtEligS (p ℓb q' : ℕ) (rest : RegChain) (LGs : LayeredGarden 1) : Prop where
  hq' : q' ≤ ℓb
  leS : ∀ a, LGs.layer a ≤ p
  rS : LGs.layer (GNode.root LGs.garden.tree 0) ≤ ℓb
  loneS : ∀ a : GNode LGs.garden.tree, a.1.2 = rest.lonePath → LGs.layer a = q'
  cohS : LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) = 0 → IsCoherentTreeAt p ℓb q' rest LGs

theorem RtEligP.qR_le {p ℓ₀ ℓb : ℕ} {ζ : ℤˣ} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (E : RtEligP p ℓ₀ ℓb ζ m Qr Qg inner LGi LGr LGg)
    (t : Fin 2) : tc2aQR m inner ζ ℓ₀ ℓb t ≤ p := by
  unfold tc2aQR; split_ifs
  · exact E.hℓ₀
  · exact E.hℓb.trans E.hℓ₀

theorem RtEligP.qG_le {p ℓ₀ ℓb : ℕ} {ζ : ℤˣ} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (E : RtEligP p ℓ₀ ℓb ζ m Qr Qg inner LGi LGr LGg)
    (t : Fin 2) : tc2aQG m inner ζ ℓ₀ ℓb t ≤ p := by
  unfold tc2aQG; split_ifs
  · exact E.hℓ₀
  · exact E.hℓb.trans E.hℓ₀

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain}

/-- **The multi-layer root-cut package** (pieces on their windows, suffix, coefficients, exceptional sum, identity;
`ind ≡ 1`). -/
theorem rt_root_pack {θ : ℝ} (hθ0 : 0 ≤ θ) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b)
    (hFC : TcFC P) {c' : ℝ} (hθc : PieceLoss P θ c') {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4)
    (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
    (hwf : (RegChain.pair m Qr Qg inner rest).wf = true) (hsz : (RegChain.pair m Qr Qg inner rest).size = 2 * n)
    {ℓ₀ ℓb q' : ℕ} (E : RtEligP p ℓ₀ ℓb (LG.garden.sig 0) m Qr Qg inner LGi LGr LGg)
    (ES : RtEligS p ℓb q' rest LGs)
    (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode LG.garden.tree → Mom P.d) → ℝ) (hind1 : ∀ κ, ind κ = 1) (k : Mom P.d) :
    ∃ (c : PairE m P.d → ℂ) (A : PairE m P.d → ℝ) (W : PairE m P.d → (Fin 2 → ℝ) → ℂ) (Ks : (Fin 2 → ℝ) → ℂ),
      (∀ e, Continuous (W e)) ∧ (∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) < ⊤) ∧ Continuous Ks ∧
      rn θ (timeBoxGt (ℓb : ℝ) q') Ks < ⊤ ∧ (∀ x : Fin 2 → ℝ, x 0 ≤ x 1 → Ks x = 0) ∧
      (∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) < ⊤) ∧
      (rn θ (timeBoxGt (ℓb : ℝ) q') Ks * ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤
        ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) *
          ENNReal.ofReal (termRb P c' n (LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) +
            LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
              LGg.incoherency Qg.links) (leafSizeProduct LG B) (starCost S cω))) ∧
      (∀ T σ s' : ℝ, σ ≤ T →
        kernelProt P.L P.γ P.δ LG H
            (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
              filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
            (fun _ => T) s' (rootFix σ) k (fun _ => 0) 0 =
          ∑' e, c e * ∫ u in rootU LG m inner T σ, rootPh (A e) σ u * (Ks ![u, s'] * W e ![σ, u])) := by
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  obtain ⟨hwfs, hwfi, hwfr, hwfg⟩ := root_wf hwf
  obtain ⟨ns, ni, nr, ng, hns, hni, hnr, hng, hnsum⟩ := root_sizes hsz
  obtain ⟨hHs, hHi, hHr, hHg⟩ := root_leafwise D hH
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  have hbℓ : (ℓb : ℝ) ≤ ℓ₀ := by exact_mod_cast E.hℓb
  have hcl : ∀ x ∈ timeBoxGt (ℓ₀ : ℝ) ℓb, x ∈ closure (interior (timeBoxGt (ℓ₀ : ℝ) ℓb)) := fun x hx =>
    VineEstS3.timeBoxGt_subset_closure_interior hbℓ hx
  set ζ := LG.garden.sig 0 with hζ
  -- the multiplier
  have hMf := star_root_mult D S ω F M Fu Mu ind hind1
  have hMc := star_root_Mc_le D S ω cω hpres F M Fu Mu
  have hGs := pull_pres (J := 30 * P.d) D.ιS hpres
  have hGi := pull_pres (J := 30 * P.d) D.ιI hpres
  have hGr := pull_pres (J := 30 * P.d) D.ιR hpres
  have hGg := pull_pres (J := 30 * P.d) D.ιG hpres
  set βs : GBranch LGs.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inr y) with hβs
  set βi : GBranch LGi.garden.tree → GBranch LG.garden.tree := fun x => D.gd.ofSum (.inl (D.hp.βi x)) with hβi
  set βr : GBranch LGr.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inl (D.hp.βr y)) with hβr
  set βg : GBranch LGg.garden.tree → GBranch LG.garden.tree := fun y => D.gd.ofSum (.inl (D.hp.βg y)) with hβg
  set ms := pullMult D.ιS βs S ω F M Fu Mu with hms
  set mi := pullMult D.ιI βi S ω F M Fu Mu with hmi
  set mr := pullMult D.ιR βr S ω F M Fu Mu with hmr
  set mg := pullMult D.ιG βg S ω F M Fu Mu with hmg
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
  -- the pieces as time functions
  set Ks : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGs
    (rootHs m inner H) (fun _ => x 0) (x 1) k (fun _ => 0) 0 ms with hKs
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
  have hKsc : Continuous Ks :=
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGs (rootHs m inner H) D.decS ms Bs hmsB _
      (summable_coset_piece hHs hL1 _)
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
  -- the gates on the pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gs := LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) with hgs
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set bs : ℝ := P.L ^ c' * rb P ns gs * leafSizeProduct LGs (rootBs m inner B) *
    starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) with hbs
  set bi : ℝ := P.L ^ c' * rb P ni gi * leafSizeProduct LGi (cutBi .nil m B) *
    starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) with hbi
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
    starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg .nil m inner ζ B) *
    starCost (pullS D.ιG S) (fun z => cω (D.ιG z)) with hbg
  have hKsb : rn θ (timeBoxGt (ℓb : ℝ) q') Ks ≤ ENNReal.ofReal bs := by
    rw [hbs, ← piece_conv hL0 hrb _ _ c' ns gs _]
    exact tc_tree_mixed K hFC hp (hle_n ns (by omega)) hθc rest LGs hwfs hns D.decS ES.leS (q := ℓb) (q' := q')
      ES.hq' (E.hℓb.trans E.hℓ₀) ES.rS ES.loneS ES.cohS _ _ _ hGs _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu)
      (rootHs m inner H) (rootBs m inner B) hHs k
  have hKib : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← piece_conv hL0 hrb _ _ c' ni gi _]
    exact tc_tree_mixed K hFC hp (hle_n ni (by omega)) hθc inner LGi hwfi hni D.decI E.leI (q := ℓ₀) (q' := ℓb)
      E.hℓb E.hℓ₀ E.rI E.loneI E.cohI _ _ _ hGi _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu)
      (cutHi .nil m H) (cutBi .nil m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rt_coupleR_oriented (fr e) m inner ζ ℓ₀ ℓb).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb _ _ c' nr gr _]
    exact tc_couple_mixed K hFC hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR E.leR (E.qR_le 0) (E.qR_le 1)
      (E.rR 0) (E.rR 1) E.cohR _ _ _ hGr _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rt_coupleG_oriented (fg e) m inner ζ ℓ₀ ℓb).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb _ _ c' ng gg _]
    exact tc_couple_mixed K hFC hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG E.leG (E.qG_le 0) (E.qG_le 1)
      (E.rG 0) (E.rG 1) E.cohG _ _ _ hGg _ _ (pull_scale _ hM) _ _ (pull_scale _ hMu) _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfini : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kr e) * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Kg e) := fun e =>
    rn_mul_le hθ0 hcl (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤
      T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 hcl (Ki e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfini e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (Ki e) *
          rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal bi *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKib e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  have hWfin : ∀ e, rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) < ⊤ := fun e =>
    (hWb e).trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ ?_)) <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- the suffix vanishes below the port
  have hKs_prot : ∀ x : Fin 2 → ℝ, Ks x = kernelProt P.L P.γ P.δ LGs (rootHs m inner H) ms (fun _ => x 0) (x 1)
      (fun _ => none) k (fun _ => 0) 0 := fun x => (cut_kernel_tree_m _ _ _ _ D.decS _ _ _ _ _).symm
  obtain ⟨bl, hbl⟩ := exists_loneParent D.decS D.rest_lonePath_ne
  have hvan : ∀ x : Fin 2 → ℝ, x 0 ≤ x 1 → Ks x = 0 := fun x hx => by
    rw [hKs_prot]
    exact kernelProt_eq_zero_of_le _ _ _ _ _ _ _ _ _ _ _ _ bl hbl rfl hx
  -- the coefficients
  have hHsum : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
    fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)) with hc
  have hMc' := fun A B => (hMc A B).trans (le_max_left Ca (max Bs (max Bi (max Br Bg))))
  have hms' := fun κ => (hmsB κ).trans ((le_max_left _ _).trans (le_max_right Ca (max Bs (max Bi (max Br Bg)))))
  have hmi' := fun κ => (hmiB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg))))))
  have hmr' := fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg)))))))
  have hmg' := fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right Ca (max Bs (max Bi (max Br Bg)))))))
  -- the exceptional sum
  have hcc0' : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hce' : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hMe : ‖(fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
        fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)‖ ≤ Ca := by
      refine (norm_mul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa0).trans (by rw [mul_one])
    calc ‖c e‖ = ‖c₀‖ * ‖(fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
        fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)‖ := norm_mul _ _
      _ ≤ coupling P.d P.L P.γ P.δ ^ 2 * Ca := by
          rw [norm_cutPrefactor hL0 K.hδ _ _]; exact mul_le_mul_of_nonneg_left hMe hcc0'
  have hsumfin : ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) < ⊤ := by
    set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
    set Z : ℝ≥0∞ := ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * Ca) * T4 *
      (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg) with hZ
    have hterm : ∀ e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤ Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
      calc ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e)
          ≤ ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ 2 * Ca) * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
              ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))))) :=
            mul_le_mul' (hce' e) (hWb e)
        _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
    have hle' : ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤
        Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
      refine (ENNReal.tsum_le_tsum hterm).trans ?_
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' (tsum_decay_le hd1 hL1 k)
        (tsum_decay_le hd1 hL1 k)))
    refine hle'.trans_lt (lt_top_iff_ne_top.2 ?_)
    rw [hZ, hT4]
    simp [ENNReal.mul_eq_top]
  refine ⟨c, A, W, Ks, hWc, hWfin, hKsc, hKsb.trans_lt ENNReal.ofReal_lt_top, hvan, hsumfin, ?_, ?_⟩
  · -- the exceptional sum
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
    have hterm : ∀ e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤ Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
      calc ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e)
          ≤ ENNReal.ofReal (cc * Ca) * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br *
              ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))))) :=
            mul_le_mul' (hce e) (hWb e)
        _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
    have hsum : ∑' e, ‖c e‖ₑ * rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (W e) ≤
        Z * (ENNReal.ofReal (latC P.d * P.L ^ P.d) * ENNReal.ofReal (latC P.d * P.L ^ P.d)) := by
      refine (ENNReal.tsum_le_tsum hterm).trans ?_
      rw [ENNReal.tsum_mul_left]
      refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
        exact tsum_decay_le hd1 hL1 k
    refine (mul_le_mul' hKsb hsum).trans ?_
    have hlat0 : 0 ≤ latC P.d * P.L ^ P.d := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
    have hn1 : ns + ni + nr + ng = n - 1 := by omega
    have hleaf : leafSizeProduct LG B = leafSizeProduct LGs (rootBs m inner B) *
        leafSizeProduct LGi (cutBi .nil m B) * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
          leafSizeProduct LGg (cutBg .nil m inner ζ B) := by
      rw [root_leafSize D B]; ring
    have hcost : starCost S cω = Ca * (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) *
        (starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) * (starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) *
          starCost (pullS D.ιG S) (fun z => cω (D.ιG z))))) := by
      unfold starCost
      rw [star_root_cost D S cω]
    have hprod : bs * bi * br * bg = P.L ^ (4 * c') *
        (P.C₁ ^ 3 * rb P (n - 1) (gs + gi + gr + gg)) * leafSizeProduct LG B *
          (starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) * (starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) *
            (starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) * starCost (pullS D.ιG S) (fun z => cω (D.ιG z))))) := by
      rw [hbs, hbi, hbr, hbg, hleaf, ← hn1]
      have h4 : P.L ^ (4 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ c' := by
        rw [show 4 * c' = c' + c' + c' + c' by ring, Real.rpow_add (by linarith), Real.rpow_add (by linarith),
          Real.rpow_add (by linarith)]
      have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := ns) (n₂ := ni) (n₃ := nr) (n₄ := ng)
        (g₁ := gs) (g₂ := gi) (g₃ := gr) (g₄ := gg)
      have hrbe : rb P (ns + ni + nr + ng) (gs + gi + gr + gg) = P.C₁ * (P.C₁ * P.δ) ^ (ns + ni + nr + ng) *
          P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((gs + gi + gr + gg : ℕ) : ℝ)) := rfl
      rw [h4, hrbe]
      linear_combination (P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ c' * leafSizeProduct LGs (rootBs m inner B) *
        leafSizeProduct LGi (cutBi .nil m B) * leafSizeProduct LGr (cutBr .nil m inner ζ B) *
          leafSizeProduct LGg (cutBg .nil m inner ζ B) * starCost (pullS D.ιS S) (fun z => cω (D.ιS z)) *
            starCost (pullS D.ιI S) (fun z => cω (D.ιI z)) * starCost (pullS D.ιR S) (fun z => cω (D.ιR z)) *
              starCost (pullS D.ιG S) (fun z => cω (D.ιG z))) * h4r
    have hs0 : 0 ≤ bs := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) (starCost_nonneg' _ _)
    have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa0
    have hval : bs * (cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d))) =
        termRb P c' n (gs + gi + gr + gg) (leafSizeProduct LG B) (starCost S cω) := by
      rw [termRb, hcost]
      linear_combination (cc * Ca * (latC P.d * P.L ^ P.d) ^ 2) * hprod
    rw [hZ, ← ENNReal.ofReal_mul hi0, ← ENNReal.ofReal_mul (mul_nonneg hi0 hr0), ← ENNReal.ofReal_mul hlat0]
    calc ENNReal.ofReal bs * (ENNReal.ofReal (cc * Ca) * T4 * ENNReal.ofReal (bi * br * bg) *
          ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)))
        = T4 * (ENNReal.ofReal bs * (ENNReal.ofReal (cc * Ca) * ENNReal.ofReal (bi * br * bg) *
            ENNReal.ofReal (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)))) := by ring
      _ = T4 * ENNReal.ofReal (bs * (cc * Ca * (bi * br * bg) * (latC P.d * P.L ^ P.d * (latC P.d * P.L ^ P.d)))) := by
          rw [← ENNReal.ofReal_mul hccCa,
            ← ENNReal.ofReal_mul (mul_nonneg hccCa (mul_nonneg (mul_nonneg hi0 hr0) hg0)),
            ← ENNReal.ofReal_mul hs0]
      _ ≤ _ := le_of_eq (by rw [hval])
  · -- the identity
    intro T σ s' hσT
    have hid := D.kernelProt_rootCut P.L P.γ P.δ H hHsum _ _ _ _ _ _ hMf CM hMc' hmi' hmr' hmg' hms' T s' σ hσT k
    refine hid.trans ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * ((fD3' S ω F (fun _ => false) M Fu Mu D.aR (starA m P.L k e) *
      fD3' S ω F (fun _ => false) M Fu Mu D.bR (starB m P.L k e)) * (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun (measurableSet_rootU _ _ _ _ _) fun u _ => ?_
    simp only [cut_kernel_tree_m _ _ _ _ D.decS, cut_kernel_tree_m _ _ _ _ D.decI,
      cut_kernel_couple_m _ _ _ _ D.decR, cut_kernel_couple_m _ _ _ _ D.decG]
    rfl

end WaveTurbulence.Flower.ProtRT
