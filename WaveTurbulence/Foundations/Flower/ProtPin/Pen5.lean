/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PenSub
public import WaveTurbulence.Foundations.Flower.ProtPin.PenCont
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckP5P7

/-! # D3 PROT-PIN: (P5) — `penTerm` with a nonempty interior

`X = Xp ++ pair m Qr Qg inner nil`, `inner ≠ nil`: the penultimate chain node (the terminal node of `inner`) and the
terminal node `𝔫_b` are both pinned at `s`. D2c's `kernelProt_penTerm_cfg5` is the terminal cut whose interior piece is
the `term` kernel of `inner` with upper clock `u` (o104 (P5): `T_A[K_pre Q₁Q₂(u, s) · (T_B G)(u, s)](T, s)`). `term_core`
bounds it with `W_e(x) = K_in^{term}(x₀) · Q_r Q_g(x)`; the interior factor is bounded by D3's `term` bound on the interior
as a protected sub-object (`PenSub`), and it is continuous in its upper clock (`PenCont`). Two cuts: `final_two`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem pen_size_two (Y : RegChain) (h : Y.lonePath ≠ []) : 2 ≤ Y.size := by
  cases Y with
  | nil => exact absurd rfl h
  | pair m r g i s => simp only [RegChain.size]; omega

theorem pen_pinsRoot5 (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) {inner : RegChain}
    (hin : inner.lonePath ≠ []) : ProtCfg.penTerm.pinsRoot (appendChain Xp (cpair m Qr Qg inner)) = false := by
  unfold ProtCfg.pinsRoot
  rw [pen_lonePath]
  have hlen : 1 ≤ inner.lonePath.length := List.length_pos_iff.mpr hin
  rw [Bool.eq_false_iff]
  intro h
  rw [List.isEmpty_iff] at h
  have h2 := congrArg List.length h
  simp only [List.length_dropLast, List.length_append, List.length_cons, List.length_singleton,
    List.length_nil] at h2
  omega

/-- **(P5), one output.** -/
theorem pen5_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
      (_hin : inner.lonePath ≠ [])
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg inner)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B) (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ)
      (_hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg inner)) Mt CS) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
          (leafSizeProduct LG B) CS) := by
  obtain ⟨Cc, hCc, hcore⟩ := term_core hθ0 (by linarith)
  obtain ⟨Ct, hCt, hperkT⟩ := exists_termStarPerkU hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨Cc * T4 * ENNReal.ofReal Ct, ENNReal.mul_lt_top (ENNReal.mul_lt_top hCc
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg inner D hin hsh hsz hamb s hps hsp t q'
    H B hH Mt CS hSM k
  obtain ⟨Mc, Ca, Sp, ωp, cp, Fp, Mp, Fup, Mup, Si, ωi, ci, Fi, Mi, Fui, Mui, Sr, ωr, cr, Fr, Mr, Fur, Mur,
    Sg, ωg, cg, Fg, Mg, Fug, Mug, hM, hGp, hGi, hGr, hGg, hCa, hMc, hcost⟩ := hSM D rfl
  have hsh' := hsh
  obtain ⟨hwf, hdec, hle, hch⟩ := hsh'
  obtain ⟨hwfp, hwfi, hwfr, hwfg⟩ := cut_wf D hwf
  obtain ⟨np, ni, nr, ng, hnp, hni, hnr, hng, hnsum⟩ := cut_sizes hsz
  obtain ⟨hlp, hlonep, hli, hlonei, hlr, hlg⟩ := cut_layers D hsh
  obtain ⟨hHp, hHi, hHr, hHg⟩ := cut_leafwise D hH
  obtain ⟨fP, fI, fR, fG⟩ := cut_flat D hsh hamb
  have hni1 : 1 ≤ ni := by have := pen_size_two inner hin; omega
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  set ζ := LG.garden.sig 0 with hζ
  have hle_n : ∀ j, j ≤ n → j ≤ P.N (p + 1) ^ 4 := fun j hj => hj.trans hn
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
  set Kt : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => kernelProt P.L P.γ P.δ LGi (cutHi Xp m H) mi
    (fun _ => x 0) s (ProtCfg.term.fix inner s t (x 0)) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 with hKt
  set fr : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGr
    (cutHr Xp m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 mr
    with hfr
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg Xp m inner ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fr e (cupR m inner ζ (x 0) (x 1) 0) (cupR m inner ζ (x 0) (x 1) 1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Kt e x * (Kr e x * Kg e x) with hW
  -- continuity
  have hKpc : Continuous Kp := FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGp (cutHp H) D.decP mp Bp hmpB k
    (summable_coset_piece hHp hL1 k)
  have hKtc : ∀ e, Continuous (Kt e) := fun e => by
    have h := pen_continuous_kernelProt_up P.L P.γ P.δ LGi (cutHi Xp m H) mi Bi hmiB s
      (ProtCfg.term.fix inner s t 0) (k + latticePoint P.L e.1.1) (card_lone_le_of_decodesTree D.decI)
      (summable_coset_piece hHi hL1 _)
    exact h.comp (continuous_apply 0)
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
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr Xp m inner ζ H) D.decR.1.1 mr Br hmrB _
        (summable_coset_piece hHr hL1 _))
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fg e) (cupG m inner ζ) (cupG_cases m inner ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg Xp m inner ζ H) D.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hWc : ∀ e, Continuous (W e) := fun e => (hKtc e).mul ((hKrc e).mul (hKgc e))
  -- the gates on the pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gp := LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) with hgp
  set gi := LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  set lat : ℝ := latC P.d * P.L ^ P.d with hlat
  set bp : ℝ := P.L ^ c' * rb P np gp * leafSizeProduct LGp (cutBp B) * starCost Sp cp with hbp
  set bt : ℝ := cc * lat ^ 2 * P.L ^ (4 * c') * (P.C₁ ^ 3 * rb P (ni - 1) gi) * leafSizeProduct LGi (cutBi Xp m B) *
    starCost Si ci with hbt
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr Xp m inner ζ B) * starCost Sr cr with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg Xp m inner ζ B) * starCost Sg cg with hbg
  have hKpb : rn θ (timeBoxGt p p) Kp ≤ ENNReal.ofReal bp := by
    rw [hbp, ← piece_conv hL0 hrb Sp cp c' np gp _]
    exact tree_piece_star K hp (hle_n np (by omega)) hθc Xp LGp hwfp hnp D.decP hlp hlonep fP Sp ωp cp hGp.1
      Fp Mp hGp.2.1 Fup Mup hGp.2.2 (cutHp H) (cutBp B) hHp k
  have hKtb : ∀ e, rn θ (timeBoxGt p p) (Kt e) ≤ ENNReal.ofReal (Ct * bt) := fun e => by
    have hport : ∀ ts ∈ timeBoxGt (p : ℝ) p, Kt e ts = kernelProt P.L P.γ P.δ LGi (cutHi Xp m H) mi
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix inner s t (ts 0)) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 :=
      fun ts _ => kernelProt_port_term P.L P.γ P.δ D.decI (cutHi Xp m H) mi _ s (ts 1) s t (ts 0) _
    rw [rn_congr θ hport]
    exact hperkT K hθc hp (hle_n ni (by omega)) LGi inner (pen_protShape_inner D hsh) hni
      (pen_treeAmb_inner D hamb) hin hps hsp t (p : ℝ) (cutHi Xp m H) (cutBi Xp m B) hHi mi (starCost Si ci)
      (pen_starMult_gate Si ωi ci Fi Mi Fui Mui hGi) _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fr e) (cupR m inner ζ) (cupR_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb Sr cr c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR hlr fR Sr ωr cr hGr.1
      Fr Mr hGr.2.1 Fur Mur hGr.2.2 _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m inner ζ) (cupG_cases m inner ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb Sg cg c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG Sg ωg cg hGg.1
      Fg Mg hGg.2.1 Fug Mug hGg.2.2 _ _ hHg _
  have hfinr : ∀ e, rn θ (timeBoxGt p p) (Kr e) < ⊤ := fun e =>
    (hKrb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfing : ∀ e, rn θ (timeBoxGt p p) (Kg e) < ⊤ := fun e =>
    (hKgb e).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hfint : ∀ e, rn θ (timeBoxGt p p) (Kt e) < ⊤ := fun e => (hKtb e).trans_lt ENNReal.ofReal_lt_top
  have hRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) ≤
      ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kr e) * rn θ (timeBoxGt p p) (Kg e) := fun e =>
    rn_mul_le hθ0 (timeBoxGt_cl p) (Kr e) (Kg e) (hKgc e) (hfinr e) (hfing e)
  have hfinRG : ∀ e, rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x) < ⊤ := fun e =>
    (hRG e).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinr e)) (hfing e))
  have hWb : ∀ e, rn θ (timeBoxGt p p) (W e) ≤
      T4 * (ENNReal.ofReal (Ct * bt) * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
        (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))) := fun e => by
    refine (rn_mul_le hθ0 (timeBoxGt_cl p) (Kt e) (fun x => Kr e x * Kg e x) ((hKrc e).mul (hKgc e))
      (hfint e) (hfinRG e)).trans ?_
    calc ENNReal.ofReal (2 ^ θ) * rn θ (timeBoxGt p p) (Kt e) * rn θ (timeBoxGt p p) (fun x => Kr e x * Kg e x)
        ≤ ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (Ct * bt) *
            (ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
              (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))) :=
          mul_le_mul' (mul_le_mul' le_rfl (hKtb e)) ((hRG e).trans (mul_le_mul' (mul_le_mul' le_rfl (hKrb e))
            (hKgb e)))
      _ = _ := by rw [hT4]; ring
  have hWfin : ∀ e, rn θ (timeBoxGt p p) (W e) < ⊤ := fun e =>
    (hWb e).trans_lt (by
      refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_ ?_)) <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hKpfin : rn θ (timeBoxGt p p) Kp < ⊤ := hKpb.trans_lt ENNReal.ofReal_lt_top
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
          (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k (fun _ => 0) 0 =
        ∑' e, c e * ∫ u in Ioo s (ts 0), cutMod (A e) s u * (Kp ![ts 0, u] * W e ![u, s]) := by
    intro ts hts
    rw [kernelProt_penTerm_cfg5 D hin P.L P.γ P.δ H hHs Mt Mc mp mi mr mg hM CM
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
    simp only [cut_kernel_tree_m _ _ _ _ D.decP, cut_kernel_couple_m _ _ _ _ D.decR,
      cut_kernel_couple_m _ _ _ _ D.decG]
    rfl
  rw [rn_congr θ hcut]
  refine (hcore (PairE m P.d) p s q' hps hsp A c Kp W hKpc hWc hKpfin hWfin).trans ?_
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
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  set Z : ℝ≥0∞ := ENNReal.ofReal (cc * Ca) * ENNReal.ofReal bp * T4 *
    (ENNReal.ofReal (Ct * bt) * ENNReal.ofReal br * ENNReal.ofReal bg) with hZ
  have hterm : ∀ e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
    calc ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e))
        ≤ ENNReal.ofReal (cc * Ca) * (ENNReal.ofReal bp * (T4 * (ENNReal.ofReal (Ct * bt) *
            ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) * (ENNReal.ofReal bg * ENNReal.ofReal (Jg e)))))) :=
          mul_le_mul' (hce e) (mul_le_mul' hKpb (hWb e))
      _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
  have hsum : ∑' e, ‖c e‖ₑ * (rn θ (timeBoxGt p p) Kp * rn θ (timeBoxGt p p) (W e)) ≤
      Z * (ENNReal.ofReal lat * ENNReal.ofReal lat) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
      exact tsum_decay_le hd1 hL1 k
  refine (mul_le_mul' le_rfl hsum).trans ?_
  -- the algebra
  have hlat0 : 0 ≤ lat := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hsp0 := starCost_nonneg' Sp cp
  have hsi0 := starCost_nonneg' Si ci
  have hsr0 := starCost_nonneg' Sr cr
  have hsg0 := starCost_nonneg' Sg cg
  have hb0 : 0 ≤ bp := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsp0
  have ht0 : 0 ≤ bt := by
    have := Real.rpow_nonneg hL0 (4 * c')
    have := hrb (ni - 1) gi
    have := hls LGi (cutBi Xp m B)
    rw [hbt]; positivity
  have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsr0
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsg0
  have hccCa : 0 ≤ cc * Ca := mul_nonneg hcc0 hCa
  set X : ℝ := cc * Ca * bp * bt * br * bg * (lat * lat) with hX
  have hEq : ENNReal.ofReal (cc * Ca) * ENNReal.ofReal bp * T4 *
      (ENNReal.ofReal (Ct * bt) * ENNReal.ofReal br * ENNReal.ofReal bg) *
        (ENNReal.ofReal lat * ENNReal.ofReal lat) = T4 * ENNReal.ofReal Ct * ENNReal.ofReal X := by
    rw [hX, ENNReal.ofReal_mul' (p := cc * Ca * bp * bt * br * bg) (mul_nonneg hlat0 hlat0),
      ENNReal.ofReal_mul' (p := cc * Ca * bp * bt * br) hg0, ENNReal.ofReal_mul' (p := cc * Ca * bp * bt) hr0,
      ENNReal.ofReal_mul' (p := cc * Ca * bp) ht0, ENNReal.ofReal_mul' (p := cc * Ca) hb0,
      ENNReal.ofReal_mul' (p := lat) hlat0, ENNReal.ofReal_mul (p := Ct) hCt]
    ring
  rw [hEq]
  -- the real inequality
  have hn2 : np + (ni - 1) + nr + ng = n - 2 := by omega
  have hg : gp + gi + gr + gg = protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG :=
    (D.incoherency_cutTerm_of_chainIn hch).symm
  have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := np) (n₂ := ni - 1) (n₃ := nr) (n₄ := ng)
    (g₁ := gp) (g₂ := gi) (g₃ := gr) (g₄ := gg)
  have hR : P.C₁ ^ 3 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) =
      rb P np gp * rb P (ni - 1) gi * rb P nr gr * rb P ng gg := by
    rw [← hn2, ← hg, h4r]; unfold rb; push_cast; ring
  have h7 : P.L ^ (7 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ (4 * c') := by
    rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
    ring_nf
  have hleafeq := cut_leafSize D B
  have hXeq : X = (P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
      (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) * leafSizeProduct LG B) *
      (Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg)))) := by
    rw [hX, hbp, hbt, hbr, hbg, h7, hleafeq,
      show P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) =
        P.C₁ ^ 3 * (P.C₁ ^ 3 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) by ring, hR]
    ring
  have hK0 : 0 ≤ P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
      (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) * leafSizeProduct LG B := by
    have := Real.rpow_nonneg hL0 (7 * c')
    have := hrb (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
    have := hls LG B
    positivity
  have hXle : X ≤ twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)
      (leafSizeProduct LG B) CS := by
    rw [hXeq, twoRb]
    calc _ ≤ (P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
          (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG)) *
            leafSizeProduct LG B) * CS := mul_le_mul_of_nonneg_left hcost hK0
      _ = _ := by rw [hcc, hlat]
  calc Cc * (T4 * ENNReal.ofReal Ct * ENNReal.ofReal X)
      ≤ Cc * (T4 * ENNReal.ofReal Ct * ENNReal.ofReal (twoRb P (7 * c') n
          (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) (leafSizeProduct LG B) CS)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hXle))
    _ = _ := by ring

/-- **(P5) for protected paired trees in `X^{θ,30d,0}`** (stars, filters, dagger; the weight `θ = η`). -/
theorem pen_final5 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} {inner : RegChain} (_D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
      (_hin : inner.lonePath ≠ [])
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg inner)) LG)
      (_hsz : protSize (appendChain Xp (cpair m Qr Qg inner)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain Xp (cpair m Qr Qg inner)) LG)
      {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t) (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
      XNormRestr θ (30 * P.d) 0 (ProtCfg.penTerm.box (appendChain Xp (cpair m Qr Qg inner)) t p q')
        (latticeBall P.L b₀ c₀)
        (fun ts k => kernelProt P.L P.γ P.δ LG H
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
            filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
          (fun _ => ts 0) (ts 1) (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t (ts 0)) k
          (fun _ => 0) 0) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) *
          regBound P n (protIncoh (appendChain Xp (cpair m Qr Qg inner)) LG) *
            ENNReal.ofReal (leafSizeProduct LG B) := by
  obtain ⟨C, hC, hperk⟩ := pen5_perk hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg inner D hin
    hsh hsz hamb s t hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hsz' : (appendChain Xp (cpair m Qr Qg inner)).size = 2 * n := hsz
  have hn2 : 2 ≤ n := by
    obtain ⟨_, ni, _, _, -, hni, -, -, h⟩ := cut_sizes hsz'
    have := pen_size_two inner hin
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  rw [prod_ofReal_starCost, box_of_pinsRoot_false (pen_pinsRoot5 Xp m Qr Qg hin)]
  refine final_two (a := 7 * 0) K.hL K.hδ hC1 ENNReal.toReal_nonneg hCL (by norm_num) hc hLOE hbig2 _ b₀ c₀ _
    hn2 hleaf (starCost_nonneg' S cω) fun k => ?_
  rw [← mul_ofReal_toReal hC (twoRb_nonneg hC1 K.hδ hL0 _ _ _ hleaf (starCost_nonneg' S cω))]
  exact hperk K hθc hp hn D hin hsh hsz' (treeAmb_of_protAmbient hamb) hps (hst.trans htp) t q' H B hH _ _
    (starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind) k

end WaveTurbulence.Flower.ProtPin
