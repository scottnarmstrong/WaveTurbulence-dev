/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Ghost.P1CoverE
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Ghost.P2D3E
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.ChainLow
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKChain.Chain
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Cov6
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Pot1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainLow
/-! **Ghost assembly for L8-H2 (E): the marked chain cover** (RULING R194; wt-l6ghost).

`chainCoverLowLE'_holds : ChainCoverLowLE'` — L8-H2's single named input (`H2/ChainLow.lean`, class `MKLowInputs`). The
proof is main's `chain_coverLLE` (FinalMKChain/ChainE) with the bank: Phases 4 and 3 are L8-H2's `P4E`, `P3E`; Phase 2
and the Step D3 phase are their bank versions `P2bankE`, `PD3bankE` (`P2D3E`); Phase 1 is `phase1_bank_coverLE`
(`P1CoverE`) with L8-H2's potential steps for `g1E32` (`hW1E`, `hW1DE`, `hW3E`, `hWRCE` at `splitK·N·3·5^d` for vine
and triple nodes) and coverage `hmemAtLE_of_inputs`; the terminal bound goes through `PD3bankE` with the bank (no
re-cut pending at `Stuck1E`: `g1E32 = g1`); bank `0` at the initial state. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.Flower.H2.Ghost
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence.GammaLow.FinalCount.Ghost

/-- **The marked chain cover (R194)**: L8-H2's `ChainCoverLowLE'`. -/
theorem chainCoverLowLE'_holds : ChainCoverLowLE' := by
  intro V _ D₀ _ _ d _ M₀ m Rn L γ η δ C₁ w P A0 C Un Fst E crit CA CN CD CR ν HR hS hp0 hP hP0 c hnc hExA hExN hExD
    hExR hExC hν hSrc hdec h0 hη40 hγ0 h2 hηγ hmate hdisj hFst hsgC hdesC hsh hHC hcrit hsd hobl hchain hshape hcritE
    N hN ε0 Fmax Yp hYp0 hYpd hε0 hCA hCN hCD hCR hNC1' hNCD hNCR hK3 hNC3' hN2 hN3 hN4 hND3 hK2 hNC2' hK4 hNC4
    hend hterm hInit
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL0 : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have h35 : (1 : ℝ) ≤ 3 * 5 ^ d := by have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num); linarith
  have hsK : (1 : ℝ) ≤ (splitK : ℝ) := by unfold splitK; norm_num
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans ?_ hNC3'
    have h1 : (1 : ℝ) ≤ (splitK : ℝ) * (3 * 5 ^ d) := by nlinarith
    have h2' : max (cAlpha d γ η) (cBeta η c) ≤ (splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h2' hN0
  have hH : ∀ κ ∈ A0, HingeSG C.toCollData L γ η w κ := fun κ hκ => SubproOblGMK.hingeSGP (hobl κ hκ)
  -- phases 4, 3 (L8-H2's), 2 and D3 (with the bank)
  have P4 := P4E (Un := Un) (Fst := Fst) (E := E) (crit := crit) HR hS hp0 hP hP0 c hnc N Yp hYp0 hN4 hK4 hNC4 hterm
  have P3 := P3E HR hS hp0 hP hP0 c hnc N Yp hYp0 hH h0 h2 hN3 hK3 hNC3 P4
  have P2 := P2bankE HR hS hp0 hP hP0 c hnc N Yp hYp0 h0 h2 hN2 hK2 hNC2' P3
  have PD3 := PD3bankE HR hS hp0 N Yp hYp0 hN4 hYpd hε0 hND3 hγ0 P2
  -- phase 1, with the bank
  have hNC1 : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max CA CN ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC1'; push_cast; ring
  have hNC3s : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC3'; push_cast; ring
  have hW1 : ∀ (h : HSt V D₀) (t : T1 h) (R' : ℕ), ApPos h.s → Good R' h.s →
      FinalCount.H.Node1 C.toCollData crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h
        (FinalCount.H.post1 C.toCollData crit L γ η h t)) * ((N : ℝ≥0∞) ^ 5 *
        WPot L γ η (Yp (RofS (FinalCount.H.post1 C.toCollData crit L γ η h t).s)) (g1E32 γ η crit Fmax E)
          (FinalCount.H.post1 C.toCollData crit L γ η h t))) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h := by
    intro h t R' hap hg hn
    rw [cast_three_five d]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 5)
      (hW1E (E := E) hL1 hη0 Yp hYp0 crit Fmax hCA hCN (splitK * N * (3 * 5 ^ d)) hNC1 hap hg hn)
  have hW1D : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s →
      FinalCount.H.Node1D C.toCollData crit h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CD * excessRHS2 L γ η [] 1 2) * ((N : ℝ≥0∞) ^ 5 *
        WPot L γ η (Yp (RofS (FinalCount.H.post1D C.toCollData crit h t).s)) (g1E32 γ η crit Fmax E)
          (FinalCount.H.post1D C.toCollData crit h t))) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h := by
    intro h t R' hap hg hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hW1DE (E := E) hL1 hη0 hη40 hγ0 ε0 Yp hYp0 hYpd hε0 crit Fmax hCD N hNCD hap hg hn)
  have hW3' : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀) (R' : ℕ),
      Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → ApPos h.s → Good R' h.s → (∃ k, k ∈ A) →
      UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h'.s)) (g1E32 γ η crit Fmax E) h')) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h := by
    intro A h h' R' hA hap hg hne hs
    have e2 : (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h' : ℝ) =
        ((3 * 5 ^ d : ℕ) : ℝ) * (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') := by push_cast; ring
    rw [e2]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 5)
      (hW3E (E := E) hL1 hη0 Yp hYp0 crit Fmax _ hγ0 hK3 (splitK * N * (3 * 5 ^ d)) hNC3s hap hg hne hs)
  have hγη : 5 * η ≤ γ := by have := HR.hη1; have := HR.hη; linarith
  have hWRC : ∀ (h : HSt V D₀) (t : T1D h) (R' : ℕ), ApPos h.s → Good R' h.s →
      Node1RC C.toCollData crit E L γ η h t →
      (N : ℝ≥0∞) * (ENNReal.ofReal (CR * excessRHS2 L γ η [] 1 2) * ((N : ℝ≥0∞) ^ 5 *
        WPot L γ η (Yp (RofS (post1RC C.toCollData crit E L γ η h t).s)) (g1E32 γ η crit Fmax E)
          (post1RC C.toCollData crit E L γ η h t))) ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h := by
    intro h t R' hap hg hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5)
      (hWRCE hL1 hη0 hη40 hγ0 hγη ε0 Yp hYp0 hYpd hε0 crit Fmax hCR N hNCR hap hg hn)
  have hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, Stuck1E C L γ η w Un E k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    intro A h b hA hb hst
    by_cases hAe : A = ∅
    · subst hAe; simp [QS_empty]
    have hap := (hA.2.resolve_left hAe).2.1
    have hF := hend A h hA hAe hst
    obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
    have hst' : Stuck1E C L γ η w Un E κ h := hst κ hκ
    have hpend : pendRCG E h = 0 := by
      unfold pendRCG
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact hi.1 (hst'.2.2 i)
    have hD3 : Inv3L M₀ Rn (ReachD3E C Un Fst E L γ η w) L w A0 A h :=
      Inv3L.map hA fun κ hκ (hr : Reach1LE C Un Fst E L γ η w κ h) => Reach1LE.toD3 hr (hst κ hκ)
    have := PD3 h A b hD3 hb
    have hg : g1 γ η crit Fmax h ≤ gExp η crit h := by
      unfold g1
      have : 0 ≤ min γ (1 - γ) * (Fmax - (h.s.M.numComponents : ℝ)) := mul_nonneg hγ0 (by linarith)
      linarith
    have hWle : WPot L γ η (Yp (RofS h.s)) (gExp η crit) h ≤
        WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h := by
      rw [WPot_g1E32_of_pend_zero _ crit Fmax E hpend]
      exact WPot_mono hL1 (hYp0 _) (apProd_pos hL0 hap) hg
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * (((N : ℝ≥0∞) ^ 4 *
          WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr
      _ = ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
          ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by ring
      _ ≤ ((N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h) *
          ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by gcongr
  have hmem := hmemAtLE_of_inputs (crit := crit) hS.isMolecule hS HR.hL hηγ HR.hη h2 hmate h0 hdisj hFst hsgC hdesC
    hsh hHC hcrit hsd hobl hchain hshape hcritE
  have key := phase1_bank_coverLE HR hS hp0 hP hP0 c hnc hExA hExN hExD hExR hExC hν hSrc hdec h0 N hN
    (fun h => (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E32 γ η crit Fmax E) h) hmem hW1 hW1D hW3' hWRC hfin
    (HSt.init M₀) A0 0 hInit (by rw [bank_init])
  simpa only [Nat.cast_zero, mul_zero, Real.rpow_zero, ENNReal.ofReal_one, mul_one] using key

end WaveTurbulence.GammaLow.Flower.H2.Ghost
