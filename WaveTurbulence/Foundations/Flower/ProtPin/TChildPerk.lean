/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildWrap

/-! # D3 PROT-PIN (P7): `termChild` at one output, the traced tree in the red side couple

`tc_perk_red`: D2c's `kernelProt_termChild_cfg`, the red side couple carrying the root trace of its tree `j` (at the
child `i` of `𝔫_b`, `sideFix_eq_trFix`, clocks `tc_cupR_trace`), the green one plain (`sideFix_eq_none`); `tc_core` with
the traced couple as a function of the partner clock (`TcTraceU`), the other pieces by the gates as in `term`, the
exceptional sum of `term`. Two cuts: `L · 2 (c²(latC L^d)²)² · C₁⁵ rb(n−2, g)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **(P7) at one output, the traced tree in the red side couple.** -/
theorem tc_perk_red {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cw : ℝ≥0∞, Cw < ⊤ ∧ ∀ {Ct : ℝ} (_hCt : 0 ≤ Ct) (_hT : TcTraceU θ Ct) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ}
      (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hθc : PieceLoss P θ 0) {p : ℕ} (_hp : p < P.D) {n : ℕ}
      (_hn : n ≤ P.N (p + 1) ^ 4) {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
      {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} (_D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) (i : Fin 3) (j : Fin 2)
      (_hj : rBase m inner (LG.garden.sig 0) j = bPath m inner ++ [i])
      (_hgn : ∀ j', gBase m inner (LG.garden.sig 0) j' ≠ bPath m inner ++ [i])
      (_hb : Xp.lonePath ++ (bPath m inner ++ [i]) ∈ (LG.garden.tree 0).branching)
      (_hbl : layerAt LG ((0 : Fin 1), Xp.lonePath ++ (bPath m inner ++ [i])) = p)
      {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1) (t q' : ℝ) (H : LeafProfiles 1 P.d)
      (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ)
      (_hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg inner)) Mt CS) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        Cw * ENNReal.ofReal (Ct * (P.L * (2 * (coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2) ^ 2 *
          (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B * CS))) := by
  obtain ⟨Cc, hCc, hcore⟩ := tc_core hθ0 (by linarith)
  refine ⟨Cc, hCc, ?_⟩
  intro Ct hCt hT P C₁a C₂a C₁b C₂b K hθc p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg inner D hsh hsz hamb i j hj hgn hb
    hbl s hps hsp t q' H B hH Mt CS hSM k
  obtain ⟨Mc, Ca, Sp, ωp, cp, Fp, Mp, Fup, Mup, Si, ωi, ci, Fi, Mi, Fui, Mui, Sr, ωr, cr, Fr, Mr, Fur, Mur,
    Sg, ωg, cg, Fg, Mg, Fug, Mug, hM, hGp, hGi, hGr, hGg, hCa, hMc, hcost⟩ := hSM D rfl
  have hsh' := hsh
  obtain ⟨hwf, hdec, hle, hch⟩ := hsh'
  obtain ⟨hwfp, hwfi, hwfr, hwfg⟩ := cut_wf D hwf
  obtain ⟨np, ni, nr, ng, hnp, hni, hnr, hng, hnsum⟩ := cut_sizes hsz
  obtain ⟨hlp, hlonep, hli, hlonei, hlr, hlg⟩ := cut_layers D hsh
  obtain ⟨hHp, hHi, hHr, hHg⟩ := cut_leafwise D hH
  obtain ⟨fP, fI, fR, fG⟩ := cut_flat D hsh hamb
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  set ζ := LG.garden.sig 0 with hζ
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
  -- the traced red couple
  have hambr := (tc_cut_side_amb D hamb).1
  have hjb := tc_red_root_branch D hj hb
  have hjl : layerAt LGr (j, []) = p := by
    have hm : ([] : TTree.Path) ∈ (LGr.garden.tree j).nodes := TTree.branching_subset_nodes _ hjb
    calc layerAt LGr (j, []) = LGr.layer ⟨(j, []), hm⟩ := layerAt_node LGr (⟨(j, []), hm⟩ : GNode LGr.garden.tree)
      _ = layerAt LG ((0 : Fin 1), Xp.lonePath ++ (rBase m inner ζ j ++ [])) := D.layR _
      _ = p := by rw [List.append_nil, hj]; exact hbl
  have hnr1 : 1 ≤ nr := tc_size_pos hwfr D.decR hjb hnr
  -- the piece multipliers and their bounds
  set mp := gateM Sp ωp Fp Mp Fup Mup with hmp
  set mi := gateM Si ωi Fi Mi Fui Mui with hmi
  set mr := gateM Sr ωr Fr Mr Fur Mur with hmr
  set mg := gateM Sg ωg Fg Mg Fug Mug with hmg
  set Bp : ℝ := (∏ a ∈ Sp, max (cp a) 0) * FiltCoh.chiDSup ^ Fp.card * FiltCoh.chiDSup ^ Fup.card with hBp
  set Bi : ℝ := (∏ a ∈ Si, max (ci a) 0) * FiltCoh.chiDSup ^ Fi.card * FiltCoh.chiDSup ^ Fui.card with hBi
  set Br : ℝ := (∏ a ∈ Sr, max (cr a) 0) * FiltCoh.chiDSup ^ Fr.card * FiltCoh.chiDSup ^ Fur.card with hBr
  set Bg : ℝ := (∏ a ∈ Sg, max (cg a) 0) * FiltCoh.chiDSup ^ Fg.card * FiltCoh.chiDSup ^ Fug.card with hBg
  have hmpB : ∀ κ, ‖mp κ‖ ≤ Bp := FiltCoh.norm_d5Mult_le Sp ωp cp hGp.1 Fp (fun _ => false) Mp Fup Mup
  have hmiB : ∀ κ, ‖mi κ‖ ≤ Bi := FiltCoh.norm_d5Mult_le Si ωi ci hGi.1 Fi (fun _ => false) Mi Fui Mui
  have hmrB : ∀ κ, ‖mr κ‖ ≤ Br := FiltCoh.norm_d5Mult_le Sr ωr cr hGr.1 Fr (fun _ => false) Mr Fur Mur
  have hmgB : ∀ κ, ‖mg κ‖ ≤ Bg := FiltCoh.norm_d5Mult_le Sg ωg cg hGg.1 Fg (fun _ => false) Mg Fug Mug
  -- the pieces as time functions
  set Kp : (Fin 2 → ℝ) → ℂ := fun x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGp (cutHp H) (fun _ => x 0) (x 1) k
    (fun _ => 0) 0 mp with hKp
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGi (cutHi Xp m H)
    (fun _ => x 0) (x 1) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 mi with hKi
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg Xp m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1) with hKg
  set V : PairE m P.d → ℝ → ℂ := fun e u => kernelProt P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) mr
    (fun b => if b.1.1 = j then s else u) 0 (trFix j s) (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 with hV
  -- continuity
  have hKpc : Continuous Kp := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGp (cutHp H) D.decP mp Bp hmpB k
    (summable_coset_piece hHp hL1 k)
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi Xp m H) D.decI mi Bi hmiB _
      (summable_coset_piece hHi hL1 _)
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    tc_oriented_cont (f := fg e) (cupG m inner ζ) (cupG_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) D.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hVc : ∀ e, Continuous (V e) := fun e => by
    have h := tc_cont_clock P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) mr Br hmrB (fun b => ¬ (b.1.1 = j))
      (fun _ => s) 0 (trFix j s) (k + latticePoint P.L e.1.2.1) (card_lone_le_of_plain D.decR.1.1)
      (summable_coset_piece hHr hL1 _)
    refine h.congr fun u => ?_
    simp only [hV]
    congr 1
    funext b
    by_cases hb' : b.1.1 = j <;> simp [hb']
  -- the gates on the pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gp := LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) with hgp
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set bp : ℝ := rb P np gp * leafSizeProduct LGp (cutBp B) * starCost Sp cp with hbp
  set bi : ℝ := rb P ni gi * leafSizeProduct LGi (cutBi Xp m B) * starCost Si ci with hbi
  set bg : ℝ := rb P ng gg * leafSizeProduct LGg (cutBg Xp m inner ζ B) * starCost Sg cg with hbg
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  set lat : ℝ := latC P.d * P.L ^ P.d with hlat
  set Rv : ℝ := P.L * (cc * (P.C₁ ^ 2 * rb P (nr - 1) gr) *
    leafSizeProduct LGr (cutBr Xp m inner ζ B) * starCost Sr cr) with hRv
  have h0r : ∀ (j g : ℕ), P.L ^ (0 : ℝ) * rb P j g = rb P j g := fun j g => by rw [Real.rpow_zero, one_mul]
  have hKpb : rn θ (timeBoxGt p p) Kp ≤ ENNReal.ofReal bp := by
    have h := tree_piece_star K hp (hle_n np (by omega)) hθc Xp LGp hwfp hnp D.decP hlp hlonep fP Sp ωp cp hGp.1
      Fp Mp hGp.2.1 Fup Mup hGp.2.2 (cutHp H) (cutBp B) hHp k
    rw [piece_conv hL0 hrb Sp cp 0 np gp _, h0r] at h
    exact h
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    have h := tree_piece_star K hp (hle_n ni (by omega)) hθc inner LGi hwfi hni D.decI hli hlonei fI Si ωi ci hGi.1
      Fi Mi hGi.2.1 Fui Mui hGi.2.2 (cutHi Xp m H) (cutBi Xp m B) hHi (k + latticePoint P.L e.1.1)
    rw [piece_conv hL0 hrb Si ci 0 ni gi _, h0r] at h
    exact h
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * f e.1.2.2 := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    have h := couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG Sg ωg cg hGg.1
      Fg Mg hGg.2.1 Fug Mug hGg.2.2 _ _ hHg (k + latticePoint P.L e.1.2.2)
    rw [piece_conv hL0 hrb Sg cg 0 ng gg _, h0r] at h
    exact h
  have hVb : ∀ e, rn θ (win p) (fun y => V e (y 0)) ≤
      ENNReal.ofReal (Ct * Rv) * tcWt P.L (k + latticePoint P.L e.1.2.1) := fun e =>
    hT K hθc hp (hle_n nr (by omega)) Qr LGr hwfr hnr D.decR hlr hambr j hjl hjb
      hps hsp (cutHr Xp m inner ζ H) (cutBr Xp m inner ζ B) hHr Sr ωr cr hGr.1 Fr Mr hGr.2.1 Fur Mur hGr.2.2
      (k + latticePoint P.L e.1.2.1)
  have hKpfin : rn θ (timeBoxGt p p) Kp < ⊤ := hKpb.trans_lt ENNReal.ofReal_lt_top
  have hfini : ∀ e, rn θ (timeBoxGt p p) (Ki e) < ⊤ := fun e => (hKib e).trans_lt ENNReal.ofReal_lt_top
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfinv : ∀ e, rn θ (win p) (fun y => V e (y 0)) < ⊤ := fun e =>
    (hVb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tc_tcWt_lt_top hd1 hL1 _))
  -- the cut identity on the box
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set CM : ℝ := max Ca (max Bp (max Bi (max Br Bg))) with hCM
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set A : PairE m P.d → ℝ := fun e => cutFreq m ζ P.L P.γ P.δ k e with hA
  set c : PairE m P.d → ℂ := fun e => c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) with hc
  have hcut : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo s (ts 0),
          cutMod (A e) s u * (Kp ![ts 0, u] * (Ki e ![u, s] * (Kg e ![u, s] * V e u))) := by
    intro ts hts
    rw [kernelProt_termChild_cfg D i P.L P.γ P.δ H hHs Mt Mc mp mi mr mg hM CM
      (fun A B => (hMc A B).trans (le_max_left _ _))
      (fun κ => (hmpB κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun κ => (hmiB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
      (fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      (fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        (le_max_right _ _)))))
      s t (ts 0) (ts 1) k, cutU_eq D hch hps hts.1.1.2, ← tsum_mul_left]
    refine tsum_congr fun e => ?_
    rw [show c e = c₀ * (Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)) from rfl, mul_assoc c₀]
    congr 1
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [sideFix_eq_trFix (rBase_injective m inner ζ) hj s, sideFix_eq_none hgn s]
    have hcl : (fun y : GBranch LGr.garden.tree => cupR m inner ζ u s y.1.1) =
        fun b => if b.1.1 = j then s else u := funext fun b => tc_cupR_trace hj u s b.1.1
    rw [hcl]
    simp only [cut_kernel_tree_m _ _ _ _ D.decP, cut_kernel_tree_m _ _ _ _ D.decI,
      cut_kernel_couple_m _ _ _ _ D.decG]
    simp only [hKp, hKi, hKg, hfg, hV, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show cutPh m ζ P.L P.γ P.δ k s e u = cutMod (A e) s u from rfl]
    ring
  rw [rn_congr θ hcut]
  refine (hcore (PairE m P.d) p s q' hps hsp A c Kp Ki Kg V hKpc hKic hKgc hVc hKpfin hfini hfing hfinv).trans ?_
  -- the exceptional sum
  have hcc0 : 0 ≤ cc := sq_nonneg _
  have hc0n : ‖c₀‖ = cc := norm_cutPrefactor hL0 K.hδ _ _
  have hce : ∀ e, ‖c e‖ₑ ≤ ENNReal.ofReal (cc * Ca) := fun e => by
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hMe : ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ ≤ Ca := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa).trans (by rw [mul_one])
    calc ‖c e‖ = ‖c₀‖ * ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ := norm_mul _ _
      _ ≤ cc * Ca := by rw [hc0n]; exact mul_le_mul_of_nonneg_left hMe hcc0
  set FF : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => tcWt P.L (k + latticePoint P.L y) with hFF
  set GG : (Fin P.d → ℤ) → ℝ≥0∞ := f with hGG
  have hFFs : ∑' y, FF y ≤ ENNReal.ofReal (2 * lat ^ 3) := tc_tsum_tcWt hd1 hL1 k
  have hGGs : ∑' y, GG y ≤ ENNReal.ofReal lat := tsum_decay_le hd1 hL1 k
  set Z : ℝ≥0∞ := ENNReal.ofReal (cc * Ca) * ENNReal.ofReal bp * ENNReal.ofReal bi * ENNReal.ofReal bg *
    ENNReal.ofReal (Ct * Rv) with hZ
  have hterm : ∀ e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * (rn θ (timeBoxGt p p) (Ki e) *
      (rn θ (timeBoxGt p p) (Kg e) * rn θ (win p) (fun y => V e (y 0))))) ≤
      Z * (FF e.1.2.1 * GG e.1.2.2) := fun e => by
    calc ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * (rn θ (timeBoxGt p p) (Ki e) *
          (rn θ (timeBoxGt p p) (Kg e) * rn θ (win p) (fun y => V e (y 0)))))
        ≤ ENNReal.ofReal (cc * Ca) * (ENNReal.ofReal bp * (ENNReal.ofReal bi *
            ((ENNReal.ofReal bg * f e.1.2.2) * (ENNReal.ofReal (Ct * Rv) * tcWt P.L (k + latticePoint P.L e.1.2.1))))) :=
          mul_le_mul' (hce e) (mul_le_mul' hKpb (mul_le_mul' (hKib e) (mul_le_mul' (hKgb e) (hVb e))))
      _ = Z * (FF e.1.2.1 * GG e.1.2.2) := by rw [hZ]; ring
  have hsum : ∑' e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * (rn θ (timeBoxGt p p) (Ki e) *
      (rn θ (timeBoxGt p p) (Kg e) * rn θ (win p) (fun y => V e (y 0))))) ≤
      Z * (ENNReal.ofReal (2 * lat ^ 3) * ENNReal.ofReal lat) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tc_tsum_pairE_le2 m FF GG).trans (mul_le_mul' hFFs hGGs))
  refine (mul_le_mul' le_rfl hsum).trans ?_
  -- the algebra
  have hlat0 : 0 ≤ lat := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hn2 : np + ni + (nr - 1) + ng = n - 2 := by omega
  have hg : gp + gi + gr + gg = protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG :=
    (D.incoherency_cutTerm_of_chainIn hch).symm
  have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := np) (n₂ := ni) (n₃ := nr - 1) (n₄ := ng)
    (g₁ := gp) (g₂ := gi) (g₃ := gr) (g₄ := gg)
  have hrb4 : rb P np gp * rb P ni gi * rb P (nr - 1) gr * rb P ng gg =
      P.C₁ ^ 3 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) := by
    rw [h4r, hn2, ← hg]
    unfold rb
    push_cast
    ring
  have hsp0 := starCost_nonneg' Sp cp
  have hsi0 := starCost_nonneg' Si ci
  have hsr0 := starCost_nonneg' Sr cr
  have hsg0 := starCost_nonneg' Sg cg
  have hb0 : 0 ≤ bp := mul_nonneg (mul_nonneg (hrb _ _) (hls _ _)) hsp0
  have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (hrb _ _) (hls _ _)) hsi0
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (hrb _ _) (hls _ _)) hsg0
  have hRv0 : 0 ≤ Rv := by
    have := hrb (nr - 1) gr
    have := hls LGr (cutBr Xp m inner ζ B)
    positivity
  have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa
  rw [hZ, ← ENNReal.ofReal_mul hccCa, ← ENNReal.ofReal_mul (mul_nonneg hccCa hb0),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hccCa hb0) hi0),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hccCa hb0) hi0) hg0),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * lat ^ 3),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hccCa hb0) hi0) hg0)
      (mul_nonneg hCt hRv0))]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  have hleaf := cut_leafSize D B
  have hrest : 0 ≤ Ct * (P.L * (2 * (cc * lat ^ 2) ^ 2 *
      (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
      leafSizeProduct LG B)) := by
    have := hrb (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
    have := hls LG B
    positivity
  have e : cc * Ca * bp * bi * bg * (Ct * Rv) * (2 * lat ^ 3 * lat) =
      Ct * (P.L * (2 * (cc * lat ^ 2) ^ 2 *
        (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
        leafSizeProduct LG B)) * (Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg)))) := by
    rw [hbp, hbi, hbg, hRv, hleaf]
    have hC5 : P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) =
        P.C₁ ^ 2 * (rb P np gp * rb P ni gi * rb P (nr - 1) gr * rb P ng gg) := by rw [hrb4]; ring
    rw [hC5]
    ring
  calc cc * Ca * bp * bi * bg * (Ct * Rv) * (2 * lat ^ 3 * lat)
      = Ct * (P.L * (2 * (cc * lat ^ 2) ^ 2 *
          (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
          leafSizeProduct LG B)) * (Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg)))) := e
    _ ≤ Ct * (P.L * (2 * (cc * lat ^ 2) ^ 2 *
          (P.C₁ ^ 5 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
          leafSizeProduct LG B)) * CS := mul_le_mul_of_nonneg_left hcost hrest
    _ = _ := by ring

end WaveTurbulence.Flower.ProtPin
