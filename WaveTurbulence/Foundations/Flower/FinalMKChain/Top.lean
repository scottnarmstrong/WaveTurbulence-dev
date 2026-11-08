/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.ChainE
public import WaveTurbulence.Foundations.Flower.FinalMKChain.Term
public import WaveTurbulence.Foundations.Flower.FinalMKChain.Num
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Ex1
public import WaveTurbulence.Foundations.FinalCount.LowChain46

/-! # C1b2 MK-CHAIN (12): `LowLoopClassBoundMK` and `LowLoopClassBoundMKAll` (the C1b target)

Copy-thread of main's LowChain45 (`low_loop_class_bound`) and LowChain46 (`low_loop_class_bound_all`) for the class
premises with survivors `LowLoopClassHypsMK` (Count.lean, R164/R164b):
- the cover chain is `chain_coverLLE` (C1b1's phase 1 with `g1E`, phases D3/2–4 here), with `Fmax = 2R − 1 + m` from
  C1b1's `hendAtLE_inv1` and the terminal bound `hterm_mainLE`;
- the re-cut constant is C1a's `ex1RC_uniform`, absorbed by `ll_numE`; the node count is `exists_NLE`;
- the survivor budget costs `L^{m + γ₀ m} ≤ L^{2m}` at the initial state (`WPot_init_eqLE`, `init_exp_leE`), which is
  the `L^{2m}` of the statement. -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.FinalCountAsm WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.VineCount

variable {d : ℕ}

/-- **The LOW class bound with survivors** (main's `low_loop_class_bound`, LowChain45, with `L^{2m}`). -/
theorem low_loop_class_boundMK (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    LowLoopClassBoundMK d γ η := by
  have hγ0 : 0 < γ := by linarith [hγ.1]
  have hγ1 : γ < 1 := hγ.2
  have hγI : γ ∈ Ioo (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : min γ (1 - γ) ≤ γ := min_le_left _ _
  have hg0' : 0 < min γ (1 - γ) := lt_min hγ0 (by linarith)
  have hη40 : η ≤ 1 / 40 := by nlinarith
  have hη1 : η < 1 := by linarith
  have hηγ : η ≤ γ := by nlinarith
  have hηsmall : 200 * η ≤ min γ (1 - γ) := by nlinarith
  have hη8 : 8 * η ≤ 2 * γ - 1 := by nlinarith
  obtain ⟨Ch, hCh1, hT⟩ := hterm_mainLE.{0, 0} hd hγ hη hsm hsm2 hηs
  obtain ⟨CsA, hCsA, C2A, hC2A, hExAall⟩ := ex1A_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  obtain ⟨CsN, C2N, hCsN, hC2N, hExNall⟩ := ex1N_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  obtain ⟨CsD, C2D, hCsD, hC2D, hExDall⟩ := ex1D_uniform hd hγI
  obtain ⟨CsR, C2R, hCsR, hC2R, hExRall⟩ := ex1RC_uniform hd γ hγI
  refine ⟨max Ch (max C2A (max C2N (max C2D C2R))), le_trans hCh1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  have hC1Ch : Ch ≤ C1 := le_trans (le_max_left _ _) hC1
  have hC1A : C2A ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC1
  have hC1N : C2N ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hC1
  have hC1D : C2D ≤ C1 := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hC1
  have hC1R : C2R ≤ C1 := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hC1
  have hC11 : 1 ≤ C1 := le_trans hCh1 hC1Ch
  obtain ⟨LA, hLA, hExA⟩ := hExAall δ hδ
  obtain ⟨LN, hLN, hExN⟩ := hExNall δ hδ
  obtain ⟨LD, hLD, hExD⟩ := hExDall δ hδ
  obtain ⟨LR, hLR, hExR⟩ := hExRall δ hδ
  obtain ⟨Rh, hRh1, hTT⟩ := hT m C1 hC1Ch δ hδ
  obtain ⟨Rq, hRq1, hq⟩ := ll_numE (d := d) hγ0 hγ1 hη hη40 hCsA hCsN hCsD hCsR m hδ
  refine ⟨LA + LN + LD + LR + Rh + Rq, ?_, fun L hL => ?_⟩
  · linarith [Real.exp_pos 1]
  have a1 : 0 ≤ LA := le_trans (Real.exp_pos 1).le hLA
  have a2 : 0 ≤ LN := le_trans (Real.exp_pos 1).le hLN
  have a3 : 0 ≤ LD := le_trans (Real.exp_pos 1).le hLD
  have a3' : 0 ≤ LR := le_trans (Real.exp_pos 1).le hLR
  have a4 : 0 ≤ Rh := by linarith
  have hLA' : LA ≤ L := by linarith
  have hLN' : LN ≤ L := by linarith
  have hLD' : LD ≤ L := by linarith
  have hLR' : LR ≤ L := by linarith
  have hRh' : Rh ≤ L := by linarith
  have hRq' : Rq ≤ L := by linarith
  have hNum := (hq L hRq').1
  have hNumR := (hq L hRq').2
  have hLe : Real.exp 1 ≤ L := hNum.hLe
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  have hlog2 := hNum.hlog2
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  have hν1 : 1 ≤ (1 + Real.log L) ^ m := one_le_pow₀ hB1
  intro V _ _ D₀ _ _ M R P A0 C mE E Un Fst crit Tm hH
  have hS := hH.subHypL
  have hMol0 := hH.isMol
  have hBsub : ∀ b ∈ loopAtoms M, b ∈ M.unloop.atoms := fun b hb => (Finset.mem_filter.1 hb).1
  have hBdeg := loopAtoms_deg_le hH.subHypLoop
  have hcard0 := hH.card_loopAtoms
  have hc4 : Fintype.card (NonLoop M) ≤ 4 * M.unloop.atoms.card := by
    have h1 := card_darts_eq_two_bonds M.unloop
    have h2 := hS.count
    omega
  obtain ⟨N, hN1, hN2, hN3, hN4, hNle⟩ := exists_NLE M.unloop.atoms.card (Fintype.card (NonLoop M)) m hLe hH.card hc4
  obtain ⟨hNC1, hNCD, hND3, hNC2, hNC3, hNC4, hN5⟩ := hNum.hN N hNle
  obtain ⟨-, hNCR, -, -, -, -, -⟩ := hNumR.hN N hNle
  have hExA' := hExA L hLA' C1 η hC1A hη hη1 hηγ (0 : Mom d) M.unloop P hH.hP0 hH.hP hMol0
  have hExN' := hExN L hLN' C1 η ((1 + Real.log L) ^ m) hC1N hη hη1 hν1 (0 : Mom d) M.unloop P hH.hP0 hH.hP hMol0
  have hExD' := hExD L hLD' C1 η ((1 + Real.log L) ^ m) hC1D hη hη1 hν1 (0 : Mom d) M.unloop C.toCollData P
  have hExR' := hExR L hLR' C1 η ((1 + Real.log L) ^ m) hC1R hη hη1 hν1 (0 : Mom d) M.unloop C.toCollData P
  have hterm := hTT L hRh' (B := loopAtoms M) (Fst := Fst) hS hH.hP hH.hP0 hH.oblE hH.trip hH.unsel hH.forbE hH.degen hH.h0
    hH.tameEq hH.mate hBsub hBdeg hH.loopTame hH.fixEff
    (fun κ hκ U hU b hb hbU => hH.noLoopSG κ hκ U (hH.sgC κ hκ U hU) b hbU hb)
    (fun κ hκ i b hb hbE => hH.noLoopSG κ hκ (E i) ((hH.oblE κ hκ).survSG i) b hbE hb) hH.critSG hH.card
    (fun A h hA hLC a => maxGap_comp hMol0 hH.hP hH.dec hH.srcGaps hA hLC a)
    (fun A h hA hLC a => maxGap_comp_op5 hMol0 hH.hP hH.dec hH.srcGaps hA hLC a)
  rw [hcard0] at hterm
  have hnc : ((2 * M.unloop.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ (2 * m) := by
    refine le_trans hH.card ?_
    rw [pow_mul]
    exact pow_le_pow_left₀ (by linarith) (one_add_le_sq hlog2) m
  have hend := hendAtLE_inv1 (Rc := R) hS hH.h0 hH.disj hH.survDisjC hH.cnBound hH.hostConnFLE
  obtain ⟨hεpos0, hε0⟩ := eps0_facts hη hη40 hη1
  have hgk : 0 < rankFactor d L γ δ C1 (M.loopBonds.card : ℤ) := by
    unfold rankFactor
    have : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := mul_pos (inv_pos.2 (by linarith)) (Real.rpow_pos_of_pos hδ.1 _)
    positivity
  have hY0 := Ypk_nonneg (L := L) hL0.le hgk.le γ η ((η ^ 5 - 4 * η ^ 6) / 2) M.loopBonds.card
  have hYd := Ypk_drop (L := L) (γ := γ) (η := η) (ε0 := (η ^ 5 - 4 * η ^ 6) / 2) hL1 hη.le hεpos0 hgk.le M.loopBonds.card
  have hap : ApPos (HSt.init M.unloop).s := by
    intro a _ R kp hcl
    change FinalCountG3.Cls.eps = FinalCountG3.Cls.alpha R kp at hcl
    cases hcl
  have hInit : Inv1LE M.unloop (R + M.loopBonds.card) C Un Fst E L γ η (0 : Mom d) A0 A0 (HSt.init M.unloop) :=
    ⟨subset_rfl, Or.inr ⟨⟨R + M.loopBonds.card, le_rfl,
      { good := ⟨hS.inv, St.init_clean M.unloop⟩, anc := AncRel.init M.unloop, rel := DartRel.init M.unloop,
        atom := (AtomRelX.init (fun _ => False) M.unloop).toU }⟩, hap, fun κ _ => Relation.ReflTransGen.refl⟩⟩
  have key := chain_coverLLE (H := ⟨hd, hγ0, hγ1, hη, le_trans hηsmall (min_le_left _ _),
      le_trans hηsmall (min_le_right _ _), hLe, hδ.1, hδ.2, hC11⟩)
    hS hH.pinned hH.hP hH.hP0 (2 * m) hnc hExA' hExN' hExD' hExR' hH.card hH.srcGaps hH.dec hH.h0 hη8 hη40 hg0'.le
    hNum.hh2 hηγ hH.mate hH.disj hH.fst hH.sgC hH.desC hH.shape hH.hostConn hH.critInt hH.survDisjC hH.oblE
    hH.survChain hH.survShape hH.survCritInt N hN1
    (Ypk L γ η ((η ^ 5 - 4 * η ^ 6) / 2) (rankFactor d L γ δ C1 (M.loopBonds.card : ℤ)) M.loopBonds.card) hY0 hYd
    (by linarith) hNum.hCA hNum.hCN hNum.hCD hNumR.hCD hNC1 hNCD hNCR hNum.hK3 hNC3 hN2 hN3 hN4 hND3 hNum.hK2 hNC2
    hNum.hK4 hNC4 hend hterm (HSt.init M.unloop) A0 hInit
  have hAdm : AdmS (fun k => k ∈ A0) (HSt.init M.unloop).s = fun k => k ∈ A0 := by
    funext k; apply propext; constructor
    · rintro ⟨k0, hk0, rfl⟩; exact hk0
    · intro hk; exact ⟨k, hk, rfl⟩
  have hq : QS L γ δ C1 0 P (HSt.init M.unloop) A0 = M.unloop.countA L γ δ C1 0 (fun k => k ∈ A0) P := by
    unfold QS; rw [hAdm]; rfl
  rw [hq] at key
  have hR1 : 1 ≤ R := hH.subHypLoop.one_le
  have hRof : RofS (HSt.init M.unloop).s = R + M.loopBonds.card := rofS_of_inv hS.inv
  have hYR : Ypk L γ η ((η ^ 5 - 4 * η ^ 6) / 2) (rankFactor d L γ δ C1 (M.loopBonds.card : ℤ)) M.loopBonds.card (R + M.loopBonds.card) =
      (rankFactor d L γ δ C1 (M.loopBonds.card : ℤ))⁻¹ * L ^ (eraseA γ η * (R : ℝ) + 4 * η * ((R : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2) := by
    unfold Ypk
    have e : (((R + M.loopBonds.card : ℕ) : ℤ) - M.loopBonds.card) = (R : ℤ) := by push_cast; ring
    rw [e, Yz_nat hR1]
  rw [hRof, hYR] at key
  have hW := WPot_init_eqLE (R := R) (γ := γ) (η := η) (ε0 := (η ^ 5 - 4 * η ^ 6) / 2) hS (inv_nonneg.2 hgk.le) hL1 crit E
  have key2 := key.trans (mul_le_mul' le_rfl hW)
  rw [loopGain_pow_eq_aux hL0 M.loopBonds.card] at key2
  have hgk' : 0 < loopGain d γ L δ C1 ^ M.loopBonds.card := by
    rw [← loopGain_pow_eq_aux hL0]; exact hgk
  have hRn : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hN5' : (N : ℝ) ^ 5 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4) := hN5
  set gk := loopGain d γ L δ C1 ^ M.loopBonds.card with hgkdef
  set Lc : ℝ := L ^ ((mE : ℝ) + min γ (1 - γ) * mE) with hLc
  set LX : ℝ := L ^ ((R - 1 : ℝ) * (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 -
    4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) with hLX
  have hLc0 : 0 ≤ Lc := by positivity
  have hLX0 : 0 ≤ LX := by positivity
  have e1 : ENNReal.ofReal gk * ((N : ℝ≥0∞) ^ 5 * (ENNReal.ofReal (gk⁻¹ * Lc) * ENNReal.ofReal LX)) =
      ENNReal.ofReal ((N : ℝ) ^ 5 * (Lc * LX)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hgk'.le) hLc0), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hgk'.le]
    congr 1
    calc gk * ((N : ℝ) ^ 5 * (gk⁻¹ * Lc * LX)) = (gk * gk⁻¹) * ((N : ℝ) ^ 5 * (Lc * LX)) := by ring
      _ = (N : ℝ) ^ 5 * (Lc * LX) := by rw [mul_inv_cancel₀ hgk'.ne', one_mul]
  calc ENNReal.ofReal gk * M.unloop.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P
      ≤ ENNReal.ofReal gk * ((N : ℝ≥0∞) ^ 5 * (ENNReal.ofReal (gk⁻¹ * Lc) * ENNReal.ofReal LX)) := by gcongr
    _ = ENNReal.ofReal ((N : ℝ) ^ 5 * (Lc * LX)) := e1
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact init_exp_leE hd hγ0 hγ1 hη hη40 hRn hL1 (by positivity) hN5' mE

/-- **C1b target: the LOW class bound with survivors, smallness form** (main's `low_loop_class_bound_all`,
LowChain46). Closes C1c's `AllGardenBoundMK` route. -/
theorem lowLoopClassBoundMKAll : LowLoopClassBoundMKAll := by
  intro d hd γ hγ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  have h2 : 0 < 2 * γ - 1 := by linarith [hγ.1]
  refine ⟨min (min γ (1 - γ) / (1000 * d)) (min ((2 * γ - 1) / (1000 * d)) (1 / (4 * 1440061))), by positivity,
    fun η hη => ?_⟩
  obtain ⟨hη0, hηle⟩ := hη
  have ha : η ≤ min γ (1 - γ) / (1000 * d) := le_trans hηle (min_le_left _ _)
  have hb : η ≤ (2 * γ - 1) / (1000 * d) := le_trans hηle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc : η ≤ 1 / (4 * 1440061) := le_trans hηle (le_trans (min_le_right _ _) (min_le_right _ _))
  refine low_loop_class_boundMK hd hγ hη0 ?_ ?_ ?_
  · rw [le_div_iff₀ (by positivity)] at ha
    nlinarith
  · rw [le_div_iff₀ (by positivity)] at hb
    nlinarith
  · rw [le_div_iff₀ (by positivity)] at hc
    nlinarith

end WaveTurbulence.Flower.FinalMKChain
