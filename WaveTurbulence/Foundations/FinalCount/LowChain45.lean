/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain44
/-! **FINALCOUNT LOW-CHAIN, session 6 (19): `low_loop_class_bound`** — the original-class loop-provenance class theorem (R79, treatment A):
`LowLoopClassBound d γ η` from `chain_coverLL` (profile `Ypk`, `gk = rankFactor |B| = loopGain^k`), `hmemAtL_of_shape`, `hendAtL_of_inputs2`
(`CnBound` at the ORIGINAL `R`), `hterm_mainL`, and the numerics `ll_num`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

variable {d : ℕ}

/-- `exists_N` with the extra node count `c_D⁴` of the D1 nodes. -/
theorem nat_poly_auxL (t : ℕ) (ht : 1 ≤ t) (x y z : ℕ) (hx : x ≤ t) (hy : y ≤ t) (hz : z ≤ t) :
    (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + y * (y * (y * y)) + 1 ≤ 4096 * t ^ 13 ∧
    nodeBound2 x y z + 1 ≤ 4096 * t ^ 13 ∧
    x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤ 4096 * t ^ 13 ∧
    x * y * y + 1 ≤ 4096 * t ^ 13 := by
  have p : ∀ k, k ≤ 13 → t ^ k ≤ t ^ 13 := fun k hk => Nat.pow_le_pow_right ht hk
  have h1 : (y * (y * (y * (y * (z * (2 * (x * 2))))))) + x * (y * (y * (z * (2 * (x * 2))))) + y * (y * (y * y)) + 1 ≤
      t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + t * (t * (t * t)) + 1 := by gcongr
  have h2 : nodeBound2 x y z + 1 ≤ nodeBound2 t t t + 1 := by unfold nodeBound2; gcongr
  have h3 : x * (y * (y * (z * (2 * (x * 2))))) + 1 ≤ t * (t * (t * (t * (2 * (t * 2))))) + 1 := by gcongr
  have h4 : x * y * y + 1 ≤ t * t * t + 1 := by gcongr
  have e1 : t * (t * (t * (t * (t * (2 * (t * 2)))))) + t * (t * (t * (t * (2 * (t * 2))))) + t * (t * (t * t)) + 1 = 4 * t ^ 6 + 4 * t ^ 5 + t ^ 4 + 1 := by ring
  have e2 : nodeBound2 t t t = 32 * t ^ 11 * (t + 1) ^ 2 := by unfold nodeBound2; ring
  have e2' : (t + 1) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have e2'' : 32 * t ^ 11 * (t + 1) ^ 2 ≤ 128 * t ^ 13 := by
    calc 32 * t ^ 11 * (t + 1) ^ 2 ≤ 32 * t ^ 11 * (4 * t ^ 2) := by gcongr
      _ = 128 * t ^ 13 := by ring
  have e3 : t * (t * (t * (t * (2 * (t * 2))))) + 1 = 4 * t ^ 5 + 1 := by ring
  have e4 : t * t * t + 1 = t ^ 3 + 1 := by ring
  have q := p 0 (by omega)
  have q3 := p 3 (by omega)
  have q5 := p 5 (by omega)
  have q6 := p 6 (by omega)
  have q4 := p 4 (by omega)
  simp only [pow_zero] at q
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; skip; skip; skip] <;> omega


theorem exists_NL (a cD m : ℕ) {L : ℝ} (hL : Real.exp 1 ≤ L) (ha : ((2 * a : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m)
    (hc : cD ≤ 4 * a) :
    ∃ N : ℕ,
      (cD * (cD * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))))) +
        (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + cD * (cD * (cD * cD)) + 1 ≤ N ∧
      nodeBound2 (2 * a) cD ⌈2 * Real.log L⌉₊ + 1 ≤ N ∧
      (2 * a) * (cD * (cD * ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * a) * 2))))) + 1 ≤ N ∧
      2 * a * cD * cD + 1 ≤ N ∧
      (N : ℝ) ≤ 4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13 := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  set ℓ : ℕ := ⌈2 * Real.log L⌉₊ + 1 with hℓ
  set t : ℕ := max (2 * a) (max cD ℓ) with ht
  have ht1 : 1 ≤ t := le_trans (by omega : 1 ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨h1, -, h3, h4⟩ := nat_poly_auxL t ht1 (2 * a) cD ℓ (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨-, h2, -, -⟩ := nat_poly_auxL t ht1 (2 * a) cD ⌈2 * Real.log L⌉₊ (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (by omega : ⌈2 * Real.log L⌉₊ ≤ ℓ) (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨4096 * t ^ 13, h1, h2, h3, h4, ?_⟩
  set T : ℝ := 2 * (1 + Real.log L) ^ (m + 1) with hT
  have hBm : (1 + Real.log L) ^ m ≤ (1 + Real.log L) ^ (m + 1) := pow_le_pow_right₀ hB1 (by omega)
  have hBm1 : 1 ≤ (1 + Real.log L) ^ (m + 1) := one_le_pow₀ hB1
  have htT : (t : ℝ) ≤ T := by
    have e1 : ((2 * a : ℕ) : ℝ) ≤ T := by rw [hT]; linarith
    have e2 : (cD : ℝ) ≤ T := by
      have : (cD : ℝ) ≤ ((4 * a : ℕ) : ℝ) := by exact_mod_cast hc
      push_cast at this e1 ha ⊢; rw [hT]; linarith
    have e3 : (ℓ : ℝ) ≤ T := by
      have h1 : (⌈2 * Real.log L⌉₊ : ℝ) < 2 * Real.log L + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : 1 + Real.log L ≤ (1 + Real.log L) ^ (m + 1) := by
        simpa using pow_le_pow_right₀ hB1 (show 1 ≤ m + 1 by omega)
      rw [hℓ]; push_cast; rw [hT]; linarith
    have : (t : ℝ) = max ((2 * a : ℕ) : ℝ) (max (cD : ℝ) (ℓ : ℝ)) := by rw [ht]; push_cast; rfl
    rw [this]; exact max_le e1 (max_le e2 e3)
  push_cast
  gcongr


theorem loopGain_pow_eq_aux {γ L δ C₁ : ℝ} (hL : 0 < L) (k : ℕ) :
    rankFactor d L γ δ C₁ (k : ℤ) = loopGain d γ L δ C₁ ^ k := rankFactor_nat_eq hL k

theorem eps0_facts {η : ℝ} (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hη1 : η < 1) :
    0 ≤ (η ^ 5 - 4 * η ^ 6) / 2 ∧ (η ^ 5 - 4 * η ^ 6) / 2 ≤ η ^ 2 / 2 := by
  have h6 : η ^ 6 = η ^ 5 * η := by ring
  have h5 : η ^ 5 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le hη1.le (by norm_num)
  have h5p := pow_pos hη 5
  have h6p := pow_pos hη 6
  have h4 : 4 * η ^ 6 ≤ η ^ 5 := by rw [h6]; nlinarith
  constructor
  · linarith
  · nlinarith

theorem low_loop_class_bound (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    LowLoopClassBound d γ η := by
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
  obtain ⟨Ch, hCh1, hT⟩ := hterm_mainL.{0, 0} hd hγ hη hsm hsm2 hηs
  obtain ⟨CsA, hCsA, C2A, hC2A, hExAall⟩ := ex1A_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  obtain ⟨CsN, C2N, hCsN, hC2N, hExNall⟩ := ex1N_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  obtain ⟨CsD, C2D, hCsD, hC2D, hExDall⟩ := ex1D_uniform hd hγI
  refine ⟨max Ch (max C2A (max C2N C2D)), le_trans hCh1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  have hC1Ch : Ch ≤ C1 := le_trans (le_max_left _ _) hC1
  have hC1A : C2A ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC1
  have hC1N : C2N ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hC1
  have hC1D : C2D ≤ C1 := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hC1
  have hC11 : 1 ≤ C1 := le_trans hCh1 hC1Ch
  obtain ⟨LA, hLA, hExA⟩ := hExAall δ hδ
  obtain ⟨LN, hLN, hExN⟩ := hExNall δ hδ
  obtain ⟨LD, hLD, hExD⟩ := hExDall δ hδ
  obtain ⟨Rh, hRh1, hTT⟩ := hT m C1 hC1Ch δ hδ
  obtain ⟨Rq, hRq1, hq⟩ := ll_num (d := d) hγ0 hγ1 hη hη40 hCsA hCsN hCsD m hδ
  refine ⟨LA + LN + LD + Rh + Rq, ?_, fun L hL => ?_⟩
  · linarith [Real.exp_pos 1]
  have a1 : 0 ≤ LA := le_trans (Real.exp_pos 1).le hLA
  have a2 : 0 ≤ LN := le_trans (Real.exp_pos 1).le hLN
  have a3 : 0 ≤ LD := le_trans (Real.exp_pos 1).le hLD
  have a4 : 0 ≤ Rh := by linarith
  have hLA' : LA ≤ L := by linarith
  have hLN' : LN ≤ L := by linarith
  have hLD' : LD ≤ L := by linarith
  have hRh' : Rh ≤ L := by linarith
  have hRq' : Rq ≤ L := by linarith
  have hNum := hq L hRq'
  have hLe : Real.exp 1 ≤ L := hNum.hLe
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  have hlog2 := hNum.hlog2
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  have hν1 : 1 ≤ (1 + Real.log L) ^ m := one_le_pow₀ hB1
  intro V _ _ D₀ _ _ M R P A0 C Un Fst crit Tm hH
  have hS := hH.subHypL
  have hMol0 := hH.isMol
  have hBsub : ∀ b ∈ loopAtoms M, b ∈ M.unloop.atoms := fun b hb => (Finset.mem_filter.1 hb).1
  have hBdeg := loopAtoms_deg_le hH.subHypLoop
  have hcard0 := hH.card_loopAtoms
  have hc4 : Fintype.card (NonLoop M) ≤ 4 * M.unloop.atoms.card := by
    have h1 := card_darts_eq_two_bonds M.unloop
    have h2 := hS.count
    omega
  obtain ⟨N, hN1, hN2, hN3, hN4, hNle⟩ := exists_NL M.unloop.atoms.card (Fintype.card (NonLoop M)) m hLe hH.card hc4
  obtain ⟨hNC1, hNCD, hND3, hNC2, hNC3, hNC4, hN5⟩ := hNum.hN N hNle
  have hExA' := hExA L hLA' C1 η hC1A hη hη1 hηγ (0 : Mom d) M.unloop P hH.hP0 hH.hP hMol0
  have hExN' := hExN L hLN' C1 η ((1 + Real.log L) ^ m) hC1N hη hη1 hν1 (0 : Mom d) M.unloop P hH.hP0 hH.hP hMol0
  have hExD' := hExD L hLD' C1 η ((1 + Real.log L) ^ m) hC1D hη hη1 hν1 (0 : Mom d) M.unloop C P
  have hterm := hTT L hRh' (B := loopAtoms M) (Fst := Fst) hS hH.hP hH.hP0 hH.obl hH.trip hH.unsel hH.degen hH.h0 hH.tameEq
    hH.mate hBsub hBdeg hH.loopTame hH.fixEff
    (fun κ hκ U hU b hb hbU => hH.noLoopSG κ hκ U (hH.sgC κ hκ U hU) b hbU hb) hH.critSG hH.card
    (fun A h hA hLC a => maxGap_comp hMol0 hH.hP hH.dec hH.srcGaps hA hLC a)
    (fun A h hA hLC a => maxGap_comp_op5 hMol0 hH.hP hH.dec hH.srcGaps hA hLC a)
  rw [hcard0] at hterm
  have hnc : ((2 * M.unloop.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ (2 * m) := by
    refine le_trans hH.card ?_
    rw [pow_mul]
    exact pow_le_pow_left₀ (by linarith) (one_add_le_sq hlog2) m
  have hmem : HmemAtL M.unloop (R + M.loopBonds.card) C Un Fst crit L γ η (0 : Mom d) A0 :=
    hmemAtL_of_shape hMol0 hS hLe hηγ hη hNum.hh2 hH.mate hH.h0 hH.disj hH.fst hH.sgC hH.desC hH.shape hH.hostConn hH.critInt
  have hend := hendAtL_of_inputs2 (Rc := R) hS hH.h0 hH.disj hH.cnBound hH.hostConnFL
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
  have hInit : Inv1L M.unloop (R + M.loopBonds.card) C Un Fst L γ η (0 : Mom d) A0 A0 (HSt.init M.unloop) :=
    ⟨subset_rfl, Or.inr ⟨⟨R + M.loopBonds.card, le_rfl,
      { good := ⟨hS.inv, St.init_clean M.unloop⟩, anc := AncRel.init M.unloop, rel := DartRel.init M.unloop,
        atom := (AtomRelX.init (fun _ => False) M.unloop).toU }⟩, hap, fun κ _ => Relation.ReflTransGen.refl⟩⟩
  have key := chain_coverLL (H := ⟨hd, hγ0, hγ1, hη, le_trans hηsmall (min_le_left _ _), le_trans hηsmall (min_le_right _ _), hLe, hδ.1, hδ.2, hC11⟩)
    hS hH.pinned hH.hP hH.hP0 (2 * m) hnc hH.obl hExA' hExN' hExD' hH.card hH.srcGaps hH.dec hH.h0 hNum.hh2 hη8 hη40 N hN1 hN2 hN3 hN4
    (Ypk L γ η ((η ^ 5 - 4 * η ^ 6) / 2) (rankFactor d L γ δ C1 (M.loopBonds.card : ℤ)) M.loopBonds.card) hY0 hYd
    (by linarith) hNum.hCA hNum.hCN hNum.hCD hNC1 hNCD hND3 hNum.hK2 hNC2 hNum.hK3 hNC3 hNum.hK4 hNC4 hg0'.le hmem
    hend hterm (HSt.init M.unloop) A0 hInit
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
  rw [hRof, hYR, WPot_init_eqL hS (inv_nonneg.2 hgk.le) hL0 crit] at key
  rw [loopGain_pow_eq_aux hL0 M.loopBonds.card] at key
  have hgk' : 0 < loopGain d γ L δ C1 ^ M.loopBonds.card := by
    rw [← loopGain_pow_eq_aux hL0]; exact hgk
  have hRn : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hN5' : (N : ℝ) ^ 5 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4) := hN5
  set gk := loopGain d γ L δ C1 ^ M.loopBonds.card with hgkdef
  have hone : ENNReal.ofReal gk * ENNReal.ofReal gk⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hgk'.le, mul_inv_cancel₀ hgk'.ne', ENNReal.ofReal_one]
  calc ENNReal.ofReal gk * M.unloop.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P
      ≤ ENNReal.ofReal gk * ((N : ℝ≥0∞) ^ 5 * (ENNReal.ofReal gk⁻¹ * ENNReal.ofReal (L ^ ((R - 1 : ℝ) *
          (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 -
          4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ)))))) := by gcongr
    _ = (N : ℝ≥0∞) ^ 5 * ENNReal.ofReal (L ^ ((R - 1 : ℝ) *
          (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 -
          4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ)))) := by
        calc _ = (ENNReal.ofReal gk * ENNReal.ofReal gk⁻¹) * ((N : ℝ≥0∞) ^ 5 * ENNReal.ofReal (L ^ ((R - 1 : ℝ) *
              (eraseA γ η + 2 * min γ (1 - γ) + 4 * η) - (η ^ 5 - 4 * η ^ 6) / 2 -
              4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))))) := by ring
          _ = _ := by rw [hone, one_mul]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        exact init_exp_le hd hγ0 hγ1 hη hη40 hRn hL1 hN5'

end WaveTurbulence.FinalCountAsm
