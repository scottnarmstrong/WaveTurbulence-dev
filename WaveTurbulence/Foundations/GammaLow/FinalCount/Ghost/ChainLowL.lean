/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChainLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain29
/-! **Ghost assembly: the low-range `chain_coverLL`** (RULING R194; design: `CHAIN-DESIGN.md`).

`chainCoverLowL'_holds : H.ChainCoverLowL'` — H-LOW's field `Src.LowInputs.chainCoverL` (`H/FinalCount/LowChainLow.lean`).
The proof is H's `chain_coverLL` (`H/FinalCount/LowChain29.lean`) with the bank: Phases 4 and 3 verbatim (`P4`, `P3`);
Phase 2 by `phase2_bank_coverL` (main's `hW2` at `splitK·N`, constant `ghostConstChain ≥ 9·25^d·ghostConstLow`); the
Step D3 phase by `phaseD3_bank_coverL` (H's potential step, the bank only drops); Phase 1 by `phase1_bank_coverL`
(H's `hW1_of` and main's `hW3_1` at `splitK·N·3·5^d`, H's Step D1 step `hW_D1'p` unchanged); bank `0` at the initial
state. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount

/-- **The low-range `chain_coverLL` (R194)**: H-LOW's `ChainCoverLowL'`. -/
theorem chainCoverLowL'_holds : H.ChainCoverLowL' := by
  intro V _ D₀ _ _ d _ M₀ Rn L γ η δ C₁ w P A0 C Un Fst crit CA CN CD ν HR hS hp0 hP hP0 c hnc hobl hExA hExN hExD
    hExC hν hSrc hdec h0 h2 hη40 N hN1 hN2 hN3 hN4 ε0 Fmax Yp hYp0 hYpd hε0 hCA hCN hCD hNC1' hNCD hND3 hK2 hNC2'
    hK3 hNC3' hK4 hNC4 hγ0 hmem hend hterm hInit
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL0 : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have hY : ∀ (R : ℕ), 0 ≤ Yp R := hYp0
  have h35 : (1 : ℝ) ≤ 3 * 5 ^ d := by have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num); linarith
  have hsK : (1 : ℝ) ≤ (splitK : ℝ) := by unfold splitK; norm_num
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans ?_ hNC3'
    have h1 : (1 : ℝ) ≤ (splitK : ℝ) * (3 * 5 ^ d) := by nlinarith
    have h2 : max (cAlpha d γ η) (cBeta η c) ≤ (splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h2 hN0
  -- phase 4
  have P4 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (H.Reach4L C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine phase4_coverL HR hS hp0 hP hP0 c hnc ?_ N hN4
      (fun h => (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn k hk hr; exact H.hext4L hn k hk hr
    · intro A h h' R' hA hap hg hne hs
      have e : RofS h'.s = RofS h.s := (rofS_ustep4 hg hs hne).trans (rofS_of_inv hg.1).symm
      have key := hW4 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit _ hK4 N γ hNC4 hap hg.1 hs
      rw [e]
      exact scale_step (a := 0) (N : ℝ≥0∞) (N : ℝ≥0∞) key
    · intro A h hA hn
      have := hterm A h hA hn
      gcongr
  -- phase 3
  have P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (H.Reach3L C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine H.phase3_coverL HR hS hp0 hP hP0 c hnc hobl (fun κ h hr => hr) ?_ h0 h2 N hN3
      (fun h => (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ z b a sg hn hdes k hk hr; exact H.hext3L hn hdes k hk hr
    · intro A h h' R' hA hap hg hne hs
      have e : RofS h'.s = RofS h.s := (rofS_ustep3 hg hs hne).trans (rofS_of_inv hg.1).symm
      have key := hW3 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit _ hK3 N hNC3 hap hg.1 hs
      rw [e]
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 2) key
    · intro A h hA hn
      have := P4 h A (hA.map fun κ hκ hr => hr.to4 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
  -- phase 2, with the bank
  have hgl : 0 ≤ ghostConstLow d c η δ := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
  have h9 : (1 : ℝ) ≤ 9 * 25 ^ d := by have : (1 : ℝ) ≤ 25 ^ d := one_le_pow₀ (by norm_num); linarith
  have hgle : 9 * 25 ^ d * ghostConstLow d c η δ ≤ H.ghostConstChain d c η δ := by
    unfold H.ghostConstChain; nlinarith [mul_nonneg hgl (by linarith : (0 : ℝ) ≤ 9 * 25 ^ d)]
  have hNC2 : ((splitK * N : ℕ) : ℝ) * H.ghostConstChain d c η δ ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC2'; push_cast; ring
  have P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3L M₀ Rn (H.Reach2L C Un Fst L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    refine phase2_bank_coverL (C := C) (Un := Un) (Fst := Fst) HR hS hp0 hP hP0 c hnc (fun κ h hr => hr) ?_ h0 h2
      N hN2 (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h n hn hdes k hk hr; exact H.hext2L hn hdes k hk hr
    · intro A h h' R' hA hap hg hne hs
      have e : RofS h'.s = RofS h.s := (rofS_ustep2 hg hs hne).trans (rofS_of_inv hg.1).symm
      have key := hW2 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit _ hK2 (splitK * N) hNC2 hap hg.1 hs
      rw [e]
      have hw := scale_step (a := 0) ((splitK * N : ℕ) : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3) key
      refine le_trans ?_ hw
      exact mul_le_mul' le_rfl (mul_le_mul' (H.ofReal_mul_le_of_le (mul_nonneg (by linarith) hgl) hgle) le_rfl)
    · intro A h hA hn
      have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
            (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) := by gcongr
        _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
  -- the Step D3 phase, with the bank
  have PD3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3L M₀ Rn (H.ReachD3 C Un Fst L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    refine phaseD3_bank_coverL (C := C) HR hS hp0 ?_ N hN4
      (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn hdes k hk hr; exact H.hextD3L hn hdes k hk hr
    · intro A h h' R' hA hap hg hne hs
      obtain ⟨k, hk⟩ := hne
      obtain ⟨v, x₁, x₂, hD, rfl⟩ := (hs.hstep hk).data
      have key := hW_D3p (L := L) (γ := γ) (η := η) hL1 hη0 hγ0 ε0 Yp hYp0 hYpd hε0 crit hg hD hap N hND3
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 4) key
    · intro A h b hA hb hn
      have := P2 h A b (hA.map fun κ hκ hr => hr.to2 (hn κ hκ)) hb
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * (((N : ℝ≥0∞) ^ 3 *
            WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr
        _ = ((N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
            ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by ring
  -- phase 1, with the bank
  have hNC1 : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max CA CN ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC1'; push_cast; ring
  have hNC3s : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC3'; push_cast; ring
  have hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s → H.Node1 C crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t)) *
        ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS (H.post1 C crit L γ η h t).s)) (g1 γ η crit Fmax)
          (H.post1 C crit L γ η h t))) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
    intro h t R' hap hg hn
    have e : RofS (H.post1 C crit L γ η h t).s = RofS h.s := (H.rofS_post1 hg.1 hn).trans (rofS_of_inv hg.1).symm
    rw [e, cast_three_five d]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 5)
      (H.hW1_of hL1 hη0 (hY (RofS h.s)) crit Fmax hCA hCN (splitK * N * (3 * 5 ^ d)) hNC1 hap hg.1 hn)
  have hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s → H.Node1D C crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * ((N : ℝ≥0∞) ^ 5 *
        WPot L γ η (Yp (RofS (H.post1D C crit h t).s)) (g1 γ η crit Fmax) (H.post1D C crit h t))) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
    intro h t R' hap hg hn
    obtain ⟨K, F, hK, -⟩ := H.node1D_spec hn
    have key := H.hW_D1'p (L := L) (γ := γ) (η := η) hL1 hη0 hη40 hγ0 ε0 Yp hYp0 hYpd hε0 crit Fmax K hg.1 hap
      F.hu F.hl F.hd2 (H.vineCut_F_lt K F.hd2) (H.vine_atoms_eps hg.1 K F.hu F.hl) F.hint
      (fun x hx => deg_le_four _ (hg.1.bounds x hx)) F.hloss hCD N hNCD
    rw [hK]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5) key
  have hW3' : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ),
      H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h'.s)) (g1 γ η crit Fmax) h')) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
    intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep3 hg hs hne).trans (rofS_of_inv hg.1).symm
    have e2 : (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h' : ℝ) =
        ((3 * 5 ^ d : ℕ) : ℝ) * (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') := by push_cast; ring
    rw [e, e2]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 5)
      (hW3_1 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit Fmax _ hγ0 hK3 (splitK * N * (3 * 5 ^ d)) hNC3s hap hg.1 hs)
  have hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), H.Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, H.Stuck1 C L γ η w Un k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
        ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    intro A h b hA hb hst
    by_cases hAe : A = ∅
    · subst hAe; simp [QS_empty]
    have hap := (hA.2.resolve_left hAe).2.1
    have hF := hend A h hA hAe hst
    have := PD3 h A b (hA.map fun κ hκ hr => hr.toD3 (hst κ hκ)) hb
    have hWle : WPot L γ η (Yp (RofS h.s)) (gExp η crit) h ≤ WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
      refine WPot_mono hL1 (hY _) (apProd_pos hL0 hap) ?_
      unfold g1
      nlinarith
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * (((N : ℝ≥0∞) ^ 4 *
          WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr
      _ = ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
          ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by ring
      _ ≤ ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h) *
          ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by gcongr
  have key := phase1_bank_coverL HR hS hp0 hP hP0 c hnc hExA hExN hExD hExC hν hSrc hdec h0 N hN1
    (fun h => (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h) hmem hW1 hW1D hW3' hfin
    (HSt.init M₀) A0 0 hInit (by rw [bank_init])
  simpa only [Nat.cast_zero, mul_zero, Real.rpow_zero, ENNReal.ofReal_one, mul_one] using key

end WaveTurbulence.GammaLow.FinalCount.Ghost
