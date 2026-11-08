/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.PenPre
public import WaveTurbulence.Foundations.Flower.ProtPin.PenRoot
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo
public import WaveTurbulence.Foundations.Flower.ProtPin.Pen5

/-! # D3 PROT-PIN: (P4) with a nonempty prefix

`X = Xp ++ pair m Qr Qg nil nil`, `Xp ≠ nil`: the penultimate node `𝔫_a` (at `Xp.lonePath`) and the terminal node `𝔫_b`
are pinned at `s`. For `T ≥ s` D2c's `kernelProt_penTerm_cfg` gives `K_pre(T, s) · V` with the constant
`V = c₀ Σ'_e Mc_e ε_e K_in Q_r Q_g (s, s)`; for `T < s` both the kernel (the free parent of `𝔫_a` lies between `s` and
`T`: `pen_kernelProt_eq_zero_of_pin`) and `K_pre(T, s)` vanish. So the kernel is `K_pre(ts 0, s) · V` on the whole box:
`V` is bounded pointwise at the diagonal (`pen_enorm_le_rn_closure`), `T ↦ K_pre(T, s)` by `pen_prefix_win` (the prefix
as a protected sub-object). Two cuts: `final_two`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl}

theorem pen_lonePath_pre (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) :
    (appendChain Xp (cpair m Qr Qg .nil)).lonePath = (Xp.lonePath ++ [m.c]) ++ [m.lone] := by
  rw [pen_lonePath]
  simp [RegChain.lonePath]

theorem pen_lonePath_ne {Y : RegChain} (hY : Y ≠ .nil) : Y.lonePath ≠ [] := by
  intro h
  have := pen_lonePath_two hY
  rw [h] at this
  simp at this

theorem pen_pinsRoot_pre {Xp : RegChain} (hXp : Xp ≠ .nil) (m : MiniTreeCode) (Qr Qg : RegCpl) :
    ProtCfg.penTerm.pinsRoot (appendChain Xp (cpair m Qr Qg .nil)) = false := by
  unfold ProtCfg.pinsRoot
  rw [pen_lonePath_pre, List.dropLast_concat, List.dropLast_concat]
  cases h : Xp.lonePath with
  | nil => exact absurd h (pen_lonePath_ne hXp)
  | cons a l => rfl

/-- **The prefix chain lies on the chain of the object.** -/
theorem pen_chainIn_prefix (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) {p : ℕ}
    (hch : ChainIn p (appendChain Xp (cpair m Qr Qg .nil)) LG) : ChainIn p Xp LGp := by
  intro b hb0 hpre hne
  have hlp := pen_lonePath_pre Xp m Qr Qg
  have hpre' : (D.βP b).1.2 <+: (appendChain Xp (cpair m Qr Qg .nil)).lonePath := by
    show b.1.2 <+: _
    rw [hlp, List.append_assoc]
    exact hpre.trans (List.prefix_append _ _)
  have hne' : (D.βP b).1.2 ≠ (appendChain Xp (cpair m Qr Qg .nil)).lonePath := by
    show b.1.2 ≠ _
    rw [hlp]
    intro h
    have h2 := congrArg List.length h
    have h3 := hpre.length_le
    simp only [List.length_append, List.length_singleton] at h2
    omega
  have h := hch (D.βP b) rfl hpre' hne'
  rw [← layerAt_node] at h
  rw [D.layP b.toNode]
  exact h

theorem pen_protShape_prefix (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) {p : ℕ}
    (hsh : ProtShape p (appendChain Xp (cpair m Qr Qg .nil)) LG) : ProtShape p Xp LGp := by
  obtain ⟨hwfp, -, -, -⟩ := cut_wf D hsh.1
  obtain ⟨hlp, -, -, -, -, -⟩ := cut_layers D hsh
  exact ⟨hwfp, D.decP, hlp, pen_chainIn_prefix D hsh.2.2.2⟩

theorem pen_treeAmb_prefix (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) {p : ℕ}
    (hA : TreeAmb p (appendChain Xp (cpair m Qr Qg .nil)) LG) : TreeAmb p Xp LGp := by
  obtain ⟨w', H, a, h, hcan, hC, hlay⟩ := hA
  have hCL := ChainEmb.of_decodesTree D.dec
  have hCLp := PL234.chainEmb_append_left hCL
  have hCp := PL234.chainEmb_append_left hC
  exact pen_treeAmb_sub hcan hlay D.decP (r := ((0 : Fin 1), [])) (by rw [D.sigP]; exact hCLp)
    (by rw [D.sigP]; exact hCp) (by simp [addrExt]) (fun z => by rw [D.layP z]; simp [addrExt])

/-- **Below the pin time the kernel vanishes**: the free parent of `𝔫_a` would lie between `s` and `T ≤ s`. -/
theorem pen_kernel_zero_pre {d : ℕ} (L γ δ : ℝ) (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg)
    (hXp : Xp ≠ .nil) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) {s t T : ℝ} (hT : T ≤ s)
    (s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t T) k
      (fun _ => 0) 0 = 0 := by
  have hl := pen_lonePath_pre Xp m Qr Qg
  have hXl := pen_lonePath_ne hXp
  have hlen := pen_lonePath_two hXp
  have hpX : Xp.lonePath <+: (appendChain Xp (cpair m Qr Qg .nil)).lonePath := by
    rw [hl, List.append_assoc]; exact List.prefix_append _ _
  have hnX : Xp.lonePath ≠ (appendChain Xp (cpair m Qr Qg .nil)).lonePath := by
    rw [hl]; intro h; have := congrArg List.length h; simp at this
  have hpd : Xp.lonePath.dropLast <+: (appendChain Xp (cpair m Qr Qg .nil)).lonePath :=
    (List.dropLast_prefix _).trans hpX
  have hnd : Xp.lonePath.dropLast ≠ (appendChain Xp (cpair m Qr Qg .nil)).lonePath := by
    rw [hl]; intro h; have := congrArg List.length h; simp at this; omega
  have hma : Xp.lonePath ∈ (LG.garden.tree 0).branching := by
    rw [D.dec.1]; exact ProtGeo.prefix_lone_branching _ _ hpX hnX
  have hmp : Xp.lonePath.dropLast ∈ (LG.garden.tree 0).branching := by
    rw [D.dec.1]; exact ProtGeo.prefix_lone_branching _ _ hpd hnd
  set a : GBranch LG.garden.tree := ⟨((0 : Fin 1), Xp.lonePath), hma⟩ with ha
  set pa : GBranch LG.garden.tree := ⟨((0 : Fin 1), Xp.lonePath.dropLast), hmp⟩ with hpa
  have hc : a.IsChildOf pa := ⟨rfl, Xp.lonePath.getLast hXl, (List.dropLast_append_getLast hXl).symm⟩
  have hd1 : (appendChain Xp (cpair m Qr Qg .nil)).lonePath.dropLast = Xp.lonePath ++ [m.c] := by
    rw [hl, List.dropLast_concat]
  have hd2 : (appendChain Xp (cpair m Qr Qg .nil)).lonePath.dropLast.dropLast = Xp.lonePath := by
    rw [hd1, List.dropLast_concat]
  have hfa : ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t T a = some s := by
    unfold ProtCfg.fix ProtCfg.pins
    rw [hd2, hd1]
    simp [ha]
  have hn1 : Xp.lonePath.dropLast ≠ Xp.lonePath := by
    intro h; have := congrArg List.length h; simp at this <;> omega
  have hn2 : Xp.lonePath.dropLast ≠ Xp.lonePath ++ [m.c] := by
    intro h; have := congrArg List.length h; simp at this <;> omega
  have e1 : (Xp.lonePath.dropLast == Xp.lonePath) = false := beq_eq_false_iff_ne.mpr hn1
  have e2 : (Xp.lonePath.dropLast == Xp.lonePath ++ [m.c]) = false := beq_eq_false_iff_ne.mpr hn2
  have hfp : ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t T pa = none := by
    unfold ProtCfg.fix ProtCfg.pins
    rw [hd2, hd1]
    simp [hpa, List.lookup, e1, e2]
  exact pen_kernelProt_eq_zero_of_pin L γ δ LG H M _ s' _ k _ _ a pa hc hfa hfp hT

/-- **(P4) with a nonempty prefix, one output.** -/
theorem pen_pre_perk {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c' : ℝ}
      (_hθc : PieceLoss P θ c') (_hC11 : 1 ≤ P.C₁) {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} (_D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) (_hXp : Xp ≠ .nil)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg .nil)) LG)
      (_hsz : (appendChain Xp (cpair m Qr Qg .nil)).size = 2 * n)
      (_hamb : TreeAmb p (appendChain Xp (cpair m Qr Qg .nil)) LG) {s : ℝ} (_hps : (p : ℝ) < s)
      (_hsp : s < p + 1) (t q' : ℝ) (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal)
      (_hH : LeafwiseControlled LG H B) (Mt : (GNode LG.garden.tree → Mom P.d) → ℂ) (CS : ℝ)
      (_hSM : StarMult P.L LG (appendChain Xp (cpair m Qr Qg .nil)) Mt CS) (k : Mom P.d),
      rn θ (timeBoxGt p q') (fun ts => kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t (ts 0)) k (fun _ => 0) 0) ≤
        C * ENNReal.ofReal (twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)
          (leafSizeProduct LG B) CS) := by
  obtain ⟨Cw, hCw, hwin⟩ := pen_prefix_win hθ0 hθ1
  set T4 : ℝ≥0∞ := ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) with hT4
  refine ⟨cutNorm θ * T4 * Cw, ENNReal.mul_lt_top (ENNReal.mul_lt_top (cutNorm_lt_top θ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)) hCw, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c' hθc hC11 p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg D hXp hsh hsz hamb s hps hsp t q'
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
  have hnp1 : 1 ≤ np := by have := pen_size_two Xp (pen_lonePath_ne hXp); omega
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
  -- the bottom pieces as time functions
  set Ki : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGi (cutHi Xp m H)
    (fun _ => x 0) (x 1) (k + latticePoint P.L e.1.1) (fun _ => 0) 0 mi with hKi
  set fr : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGr
    (cutHr Xp m .nil ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.1) (fun _ => 0) 0 mr
    with hfr
  set fg : PairE m P.d → ℝ → ℝ → ℂ := fun e a b => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LGg
    (cutHg Xp m .nil ζ H) (fun y => if y.1.1 = 0 then a else b) 0 (k + latticePoint P.L e.1.2.2) (fun _ => 0) 0 mg
    with hfg
  set Kr : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fr e (cupR m .nil ζ (x 0) (x 1) 0) (cupR m .nil ζ (x 0) (x 1) 1) with hKr
  set Kg : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x =>
    fg e (cupG m .nil ζ (x 0) (x 1) 0) (cupG m .nil ζ (x 0) (x 1) 1) with hKg
  set W : PairE m P.d → (Fin 2 → ℝ) → ℂ := fun e x => Ki e x * (Kr e x * Kg e x) with hW
  have hKic : ∀ e, Continuous (Ki e) := fun e =>
    FiltCoh.continuous_treeKW_time P.L P.γ P.δ LGi (cutHi Xp m H) D.decI mi Bi hmiB _
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
    hor (f := fr e) (cupR m .nil ζ) (cupR_cases m .nil ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGr (cutHr Xp m .nil ζ H) D.decR.1.1 mr Br hmrB _
        (summable_coset_piece hHr hL1 _))
  have hKgc : ∀ e, Continuous (Kg e) := fun e =>
    hor (f := fg e) (cupG m .nil ζ) (cupG_cases m .nil ζ)
      (FiltCoh.continuous_coupleKW_time P.L P.γ P.δ LGg (cutHg Xp m .nil ζ H) D.decG.1.1 mg Bg hmgB _
        (summable_coset_piece hHg hL1 _))
  have hWc : ∀ e, Continuous (W e) := fun e => (hKic e).mul ((hKrc e).mul (hKgc e))
  -- the gates on the bottom pieces
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hrb : ∀ j g, 0 ≤ rb P j g := fun j g => rb_nonneg hC1 K.hδ hL0 j g
  have hLc : 0 ≤ P.L ^ c' := Real.rpow_nonneg hL0 _
  have hls : ∀ {w : ℕ} (LGx : LayeredGarden w) (Bx : (Fin w × TTree.Path) → NNReal), 0 ≤ leafSizeProduct LGx Bx :=
    fun LGx Bx => Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  set gp := LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) with hgp
  set gi := LGi.incoherency (RegChain.nil.treeLinks (LGi.garden.sig 0)) with hgi
  set gr := LGr.incoherency Qr.links with hgr
  set gg := LGg.incoherency Qg.links with hgg
  set cc : ℝ := coupling P.d P.L P.γ P.δ ^ 2 with hcc
  set lat : ℝ := latC P.d * P.L ^ P.d with hlat
  set tp : ℝ := termRb P c' np gp (leafSizeProduct LGp (cutBp B)) (starCost Sp cp) with htp
  set bi : ℝ := P.L ^ c' * rb P ni gi * leafSizeProduct LGi (cutBi Xp m B) * starCost Si ci with hbi
  set br : ℝ := P.L ^ c' * rb P nr gr * leafSizeProduct LGr (cutBr Xp m .nil ζ B) * starCost Sr cr with hbr
  set bg : ℝ := P.L ^ c' * rb P ng gg * leafSizeProduct LGg (cutBg Xp m .nil ζ B) * starCost Sg cg with hbg
  have hKib : ∀ e, rn θ (timeBoxGt p p) (Ki e) ≤ ENNReal.ofReal bi := fun e => by
    rw [hbi, ← piece_conv hL0 hrb Si ci c' ni gi _]
    exact tree_piece_star K hp (hle_n ni (by omega)) hθc .nil LGi hwfi hni D.decI hli hlonei fI Si ωi ci hGi.1
      Fi Mi hGi.2.1 Fui Mui hGi.2.2 (cutHi Xp m H) (cutBi Xp m B) hHi _
  set Jr : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.1) ^ (30 * P.d))⁻¹ with hJr
  set Jg : PairE m P.d → ℝ := fun e => (jbr (k + latticePoint P.L e.1.2.2) ^ (30 * P.d))⁻¹ with hJg
  have hjpos : ∀ y : Mom P.d, 0 < jbr y ^ (30 * P.d) := fun y => pow_pos (jbr_pos y) _
  have hKrb : ∀ e, rn θ (timeBoxGt p p) (Kr e) ≤ ENNReal.ofReal br * ENNReal.ofReal (Jr e) := fun e => by
    refine (rn_couple_oriented (fr e) (cupR m .nil ζ) (cupR_cases m .nil ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbr, ← piece_conv hL0 hrb Sr cr c' nr gr _]
    exact couple_piece_star K hp (hle_n nr (by omega)) hθc Qr LGr hwfr hnr D.decR hlr fR Sr ωr cr hGr.1
      Fr Mr hGr.2.1 Fur Mur hGr.2.2 _ _ hHr _
  have hKgb : ∀ e, rn θ (timeBoxGt p p) (Kg e) ≤ ENNReal.ofReal bg * ENNReal.ofReal (Jg e) := fun e => by
    refine (rn_couple_oriented (fg e) (cupG m .nil ζ) (cupG_cases m .nil ζ)).trans ?_
    refine le_mul_inv_of_weighted (hjpos _) ?_
    rw [hbg, ← piece_conv hL0 hrb Sg cg c' ng gg _]
    exact couple_piece_star K hp (hle_n ng (by omega)) hθc Qg LGg hwfg hng D.decG hlg fG Sg ωg cg hGg.1
      Fg Mg hGg.2.1 Fug Mug hGg.2.2 _ _ hHg _
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
  -- the constant `V`
  have hHs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom P.d,
      Summable fun j : Fin P.d → ℤ => |H ℓ.1 (k' + latticePoint P.L j)| :=
    fun ℓ hℓ k' => summable_coset_piece hH hL1 k' ℓ hℓ
  set CM : ℝ := max Ca (max Bp (max Bi (max Br Bg))) with hCM
  set c₀ : ℂ := (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) with hc₀
  set Xe : PairE m P.d → ℂ := fun e =>
    kernelProt P.L P.γ P.δ LGi (cutHi Xp m H) mi (fun _ => s) s (fun _ => none) (k + latticePoint P.L e.1.1)
      (fun _ => 0) 0 *
    (kernelProt P.L P.γ P.δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) mr
        (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none) (k + latticePoint P.L e.1.2.1)
        (fun _ => 0) 0 *
      kernelProt P.L P.γ P.δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) mg
        (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none) (k + latticePoint P.L e.1.2.2)
        (fun _ => 0) 0) with hXe
  set V : ℂ := c₀ * ∑' e, Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ) * Xe e with hV
  have hXW : ∀ e, Xe e = W e ![s, s] := fun e => by
    simp only [hXe, cut_kernel_tree_m _ _ _ _ D.decI, cut_kernel_couple_m _ _ _ _ D.decR,
      cut_kernel_couple_m _ _ _ _ D.decG]
    rfl
  set Kpre : (Fin 1 → ℝ) → ℂ := fun T => kernelProt P.L P.γ P.δ LGp (cutHp H) mp (fun _ => T 0) s (fun _ => none) k
    (fun _ => 0) 0 with hKpre
  -- the kernel on the box
  have hbox : ∀ ts ∈ timeBoxGt (p : ℝ) q',
      kernelProt P.L P.γ P.δ LG H Mt (fun _ => ts 0) (ts 1)
          (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t (ts 0)) k (fun _ => 0) 0 =
        (fun T => Kpre T * V) (fun _ => ts 0) := by
    intro ts _
    by_cases hsT : s ≤ ts 0
    · rw [kernelProt_penTerm_cfg D P.L P.γ P.δ H hHs Mt Mc mp mi mr mg hM CM
        (fun A B => (hMc A B).trans (le_max_left _ _))
        (fun κ => (hmpB κ).trans ((le_max_left _ _).trans (le_max_right _ _)))
        (fun κ => (hmiB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
        (fun κ => (hmrB κ).trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          (le_max_right _ _)))))
        (fun κ => (hmgB κ).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
          (le_max_right _ _)))))
        (ts 0) s (ts 1) t hsT k]
      show _ = Kpre (fun _ => ts 0) * (c₀ * ∑' e, Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ) * Xe e)
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      refine tsum_congr fun e => ?_
      simp only [hKpre, hXe]
      ring
    · have hT : ts 0 ≤ s := (lt_of_not_ge hsT).le
      obtain ⟨b, hb⟩ := exists_loneParent D.decP (pen_lonePath_ne hXp)
      rw [pen_kernel_zero_pre P.L P.γ P.δ D hXp H Mt hT (ts 1) k]
      show (0 : ℂ) = Kpre (fun _ => ts 0) * V
      rw [show Kpre (fun _ => ts 0) = 0 from
        kernelProt_eq_zero_of_le P.L P.γ P.δ LGp (cutHp H) mp _ s _ k _ _ b hb rfl hT, zero_mul]
  rw [rn_congr θ hbox]
  refine (rn_lift hθ0 p q' (fun T => Kpre T * V)).trans ?_
  refine (mul_le_mul' le_rfl (pen_rn_mul_const_le θ (win (p : ℝ)) Kpre V)).trans ?_
  have hKw := hwin K hθc hC11 hp (hle_n np (by omega)) hXp (pen_protShape_prefix D hsh) hnp
    (pen_treeAmb_prefix D hamb) (cutHp H) (cutBp B) hHp Sp ωp cp Fp Mp Fup Mup hGp hps hsp k
  -- the bound on `V`
  have hcc0 : 0 ≤ cc := sq_nonneg _
  have hc0n : ‖c₀‖ₑ = ENNReal.ofReal cc := by rw [← ofReal_norm, norm_cutPrefactor hL0 K.hδ]
  set f : (Fin P.d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (jbr (k + latticePoint P.L y) ^ (30 * P.d))⁻¹ with hf
  set Z : ℝ≥0∞ := ENNReal.ofReal Ca * T4 * (ENNReal.ofReal bi * ENNReal.ofReal br * ENNReal.ofReal bg) with hZ
  have hterm : ∀ e, ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ) * Xe e‖ₑ ≤
      Z * (f e.1.2.1 * f e.1.2.2) := fun e => by
    have hMe : ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ)‖ₑ ≤ ENNReal.ofReal Ca := by
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (hMc _ _) (abs_cutEps_le m e) (abs_nonneg _) hCa).trans (by rw [mul_one])
    have hW1 : ‖Xe e‖ₑ ≤ rn θ (timeBoxGt p p) (W e) := by
      rw [hXW]
      exact pen_enorm_le_rn_closure hθ0 (timeBoxGt_cl p) (hWc e) (pen_diag_mem_closure hps.le hsp)
    calc ‖Mc (starA m P.L k e) (starB m P.L k e) * (cutEps m e : ℂ) * Xe e‖ₑ
        ≤ ENNReal.ofReal Ca * (T4 * (ENNReal.ofReal bi * ((ENNReal.ofReal br * ENNReal.ofReal (Jr e)) *
            (ENNReal.ofReal bg * ENNReal.ofReal (Jg e))))) := by
          rw [enorm_mul]
          exact mul_le_mul' hMe (hW1.trans (hWb e))
      _ = Z * (f e.1.2.1 * f e.1.2.2) := by rw [hZ, hf]; ring
  have hVb : ‖V‖ₑ ≤ ENNReal.ofReal cc * (Z * (ENNReal.ofReal lat * ENNReal.ofReal lat)) := by
    rw [hV, enorm_mul, hc0n]
    refine mul_le_mul' le_rfl (enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum hterm).trans ?_))
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ((tsum_pairE_le m f).trans (mul_le_mul' ?_ ?_)) <;>
      exact tsum_decay_le hd1 hL1 k
  -- the algebra
  have hlat0 : 0 ≤ lat := mul_nonneg (latC_nonneg _) (pow_nonneg hL0 _)
  have hsp0 := starCost_nonneg' Sp cp
  have hsi0 := starCost_nonneg' Si ci
  have hsr0 := starCost_nonneg' Sr cr
  have hsg0 := starCost_nonneg' Sg cg
  have htp0 : 0 ≤ tp := termRb_nonneg hC1 K.hδ hL0 _ _ (hls _ _) hsp0
  have hi0 : 0 ≤ bi := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsi0
  have hr0 : 0 ≤ br := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsr0
  have hg0 : 0 ≤ bg := mul_nonneg (mul_nonneg (mul_nonneg hLc (hrb _ _)) (hls _ _)) hsg0
  set Y : ℝ := cc * Ca * bi * br * bg * (lat * lat) * tp with hY
  have hEq : cutNorm θ * (ENNReal.ofReal cc * (Z * (ENNReal.ofReal lat * ENNReal.ofReal lat)) *
      (Cw * ENNReal.ofReal tp)) = cutNorm θ * T4 * Cw * ENNReal.ofReal Y := by
    rw [hY, hZ, ENNReal.ofReal_mul' (p := cc * Ca * bi * br * bg * (lat * lat)) htp0,
      ENNReal.ofReal_mul' (p := cc * Ca * bi * br * bg) (mul_nonneg hlat0 hlat0),
      ENNReal.ofReal_mul' (p := cc * Ca * bi * br) hg0, ENNReal.ofReal_mul' (p := cc * Ca * bi) hr0,
      ENNReal.ofReal_mul' (p := cc * Ca) hi0, ENNReal.ofReal_mul' (p := cc) hCa,
      ENNReal.ofReal_mul' (p := lat) hlat0]
    ring
  have hn2 : (np - 1) + ni + nr + ng = n - 2 := by omega
  have hg : gp + gi + gr + gg = protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG :=
    (D.incoherency_cutTerm_of_chainIn hch).symm
  have h4r := rb_four (P := P) (by linarith : (0 : ℝ) < P.L) (n₁ := np - 1) (n₂ := ni) (n₃ := nr) (n₄ := ng)
    (g₁ := gp) (g₂ := gi) (g₃ := gr) (g₄ := gg)
  have hR : P.C₁ ^ 3 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG) =
      rb P (np - 1) gp * rb P ni gi * rb P nr gr * rb P ng gg := by
    rw [← hn2, ← hg, h4r]; unfold rb; push_cast; ring
  have h7 : P.L ^ (7 * c') = P.L ^ c' * P.L ^ c' * P.L ^ c' * P.L ^ (4 * c') := by
    rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
    ring_nf
  have hleafeq := cut_leafSize D B
  have hYeq : Y = (P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
      (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)) * leafSizeProduct LG B) *
      (Ca * (starCost Sp cp * (starCost Si ci * (starCost Sr cr * starCost Sg cg)))) := by
    rw [hY, htp, termRb, hbi, hbr, hbg, h7, hleafeq,
      show P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG) =
        P.C₁ ^ 3 * (P.C₁ ^ 3 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)) by ring, hR,
      show np - 1 = np - 1 from rfl]
    ring
  have hK0 : 0 ≤ P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
      (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)) * leafSizeProduct LG B := by
    have := Real.rpow_nonneg hL0 (7 * c')
    have := hrb (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)
    have := hls LG B
    positivity
  have hYle : Y ≤ twoRb P (7 * c') n (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)
      (leafSizeProduct LG B) CS := by
    rw [hYeq, twoRb]
    calc _ ≤ (P.L ^ (7 * c') * (cc * lat ^ 2) ^ 2 *
          (P.C₁ ^ 6 * rb P (n - 2) (protIncoh (appendChain Xp (cpair m Qr Qg .nil)) LG)) *
            leafSizeProduct LG B) * CS := mul_le_mul_of_nonneg_left hcost hK0
      _ = _ := by rw [hcc, hlat]
  calc cutNorm θ * (‖V‖ₑ * rn θ (win (p : ℝ)) Kpre)
      ≤ cutNorm θ * (ENNReal.ofReal cc * (Z * (ENNReal.ofReal lat * ENNReal.ofReal lat)) *
          (Cw * ENNReal.ofReal tp)) := mul_le_mul' le_rfl (mul_le_mul' hVb hKw)
    _ = cutNorm θ * T4 * Cw * ENNReal.ofReal Y := hEq
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hYle)

/-- **(P4) with a nonempty prefix, for protected paired trees, in `X^{θ,30d,0}`** (stars, filters, dagger; the weight
`θ = η`). -/
theorem pen_final_prefix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) {c CL : ℝ}
      (_hθc : PieceLoss P θ 0) (_hc : 31 * (P.d : ℝ) + 6 ≤ c) (_hCL : 0 ≤ CL) (_hC11 : 1 ≤ P.C₁)
      (_hLOE : ∀ (L : ℝ), 1 ≤ L → ∀ {r : ℕ} (B : Set (Fin r → ℝ)) (b₀ c₀ : Mom P.d)
        (F : (Fin r → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞), (∀ k ∈ latticeBall L b₀ c₀, XNorm00Restr θ B {k} F ≤ X) →
        XNormRestr θ (30 * P.d) 0 B (latticeBall L b₀ c₀) F ≤ ENNReal.ofReal (CL * L ^ (31 * P.d)) * X)
      (_hbig2 : twoK CL Cr P.d * P.δ ^ 2 * P.C₁ ^ 4 * P.L ^ (4 * P.γ) ≤ P.L ^ (5 : ℝ))
      {p : ℕ} (_hp : p < P.D) {n : ℕ} (_hn : n ≤ P.N (p + 1) ^ 4)
      {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
      {Qr Qg : RegCpl} (_D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) (_hXp : Xp ≠ .nil)
      (_hsh : ProtShape p (appendChain Xp (cpair m Qr Qg .nil)) LG)
      (_hsz : protSize (appendChain Xp (cpair m Qr Qg .nil)) LG = 2 * n)
      (_hamb : ProtAmbient p (appendChain Xp (cpair m Qr Qg .nil)) LG)
      {s t : ℝ} (_hps : (p : ℝ) < s) (_hst : s < t) (_htp : t < p + 1) (q' : ℕ)
      (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
      (cω : GNode LG.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
      (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
      (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
      (ind : (GNode LG.garden.tree → Mom P.d) → ℝ)
      (_hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg .nil)) ind)
      (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (_hH : LeafwiseControlled LG H B)
      (b₀ c₀ : Mom P.d),
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
  obtain ⟨C, hC, hperk⟩ := pen_pre_perk hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K c CL hθc hc hCL hC11 hLOE hbig2 p hp n hn LG LGp LGi LGr LGg Xp m Qr Qg D hXp
    hsh hsz hamb s t hps hst htp q' S ω cω hpres F M hM Fu Mu hMu ind hind H B hH b₀ c₀
  have hL0 : (0 : ℝ) ≤ P.L := by linarith [K.hL]
  have hC1 : 0 ≤ P.C₁ := K.ha0.trans K.ha
  have hsz' : (appendChain Xp (cpair m Qr Qg .nil)).size = 2 * n := hsz
  have hn2 : 2 ≤ n := by
    obtain ⟨np, _, _, _, hnp, -, -, -, h⟩ := cut_sizes hsz'
    have := pen_size_two Xp (pen_lonePath_ne hXp)
    omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  rw [prod_ofReal_starCost, box_of_pinsRoot_false (pen_pinsRoot_pre hXp m Qr Qg)]
  refine final_two (a := 7 * 0) K.hL K.hδ hC1 ENNReal.toReal_nonneg hCL (by norm_num) hc hLOE hbig2 _ b₀ c₀ _
    hn2 hleaf (starCost_nonneg' S cω) fun k => ?_
  rw [← mul_ofReal_toReal hC (twoRb_nonneg hC1 K.hδ hL0 _ _ _ hleaf (starCost_nonneg' S cω))]
  exact hperk K hθc hC11 hp hn D hXp hsh hsz' (treeAmb_of_protAmbient hamb) hps (hst.trans htp) t q' H B hH _ _
    (starMult_tree S ω cω hpres F M hM Fu Mu hMu ind hind) k

end WaveTurbulence.Flower.ProtPin
