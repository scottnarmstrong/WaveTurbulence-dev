/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1G
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChainLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChain2
/-! **Ghost assembly: the low-range `chain_cover`** (RULING R194; design: `CHAIN-DESIGN.md`).

`chainCoverLow'_holds : H.ChainCoverLow'` — H-ASM's field `Src.AsmInputs.chainCover` (`H/FinalCount/AsmChainLow.lean`,
budgets with the factor `splitK`). The proof is main's `chain_cover` (H port `H/FinalCount/AsmChain2.lean`) with
Phases 1 and 2 replaced by their bank versions: Phase 4 and Phase 3 verbatim (`P4`, `P3`); Phase 2 by
`phase2_bank_cover` (`P2`: `QS h A ≤ N³·WPot(gExp)·L^{5ηb}` for `b ≥ bank h A`; potential step from main's `hW2` with
`N ↦ splitK·N` and the constant `ghostConstChain ≥ 9·25^d·ghostConstLow`); Phase 1 by `phase1_bank_cover`
(potential steps from H's `hW1_of` and main's `hW3_1` with `N ↦ splitK·N·3·5^d`), terminal bound through `P2` with the
bank. At the initial state the bank is `0` (no `α`-atoms). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- At the initial state there are no critical atoms: the bank is `0`. -/
theorem bank_init {L γ η : ℝ} {w : Mom d} (M₀ : Molecule V D₀) (A : Set (D₀ → (Fin d → ℤ))) :
    bank L γ η w (HSt.init M₀) A = 0 := by
  obtain ⟨m, hm, he⟩ := exists_matching_eq (NCEdge L γ η w (HSt.init M₀) A) (critSet L γ η (HSt.init M₀))
  unfold bank
  rw [← he, Finset.card_eq_zero]
  ext e
  simp only [notMem_empty, iff_false]
  intro he'
  obtain ⟨-, -, -, hE⟩ := hm.1 e he'
  obtain ⟨R, hR, -⟩ := hE.2.1.2.2
  have e0 : (HSt.init M₀).s.cls e.1 = .eps := rfl
  rw [e0] at hR
  cases hR

/-- Absorbing an integer factor of a cost into the node count. -/
theorem kn_absorb (KN m : ℕ) (a : ℝ) (X Y : ℝ≥0∞)
    (h : ((KN * m : ℕ) : ℝ≥0∞) * (ENNReal.ofReal a * X) ≤ Y) :
    ((KN : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((m : ℝ) * a) * X) ≤ Y := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
  calc ((KN : ℕ) : ℝ≥0∞) * ((m : ℝ≥0∞) * ENNReal.ofReal a * X) =
      ((KN * m : ℕ) : ℝ≥0∞) * (ENNReal.ofReal a * X) := by push_cast; ring
    _ ≤ Y := h

theorem cast_three_five (d : ℕ) : (3 * 5 ^ d : ℝ) = ((3 * 5 ^ d : ℕ) : ℝ) := by push_cast; ring

/-- **The low-range `chain_cover` (R194)**: H-ASM's `ChainCoverLow'`. -/
theorem chainCoverLow'_holds : H.ChainCoverLow' := by
  intro V _ D₀ _ _ d _ M₀ Rn L γ η δ C₁ w P A0 C Un Fst crit CA CN ν HR hS hp0 hP hP0 c hnc hobl hExA hExN hExC hν
    hSrc hdec h0 h2 N hN1 hN2 hN3 hN4 Y0 Fmax hY0 hCA hCN hNC1' hK2 hNC2' hK3 hNC3' hK4 hNC4 hγ0 hmem hend hterm hInit
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hL : 0 < L := by linarith
  have hη0 : 0 ≤ η := HR.hη.le
  have h35 : (1 : ℝ) ≤ 3 * 5 ^ d := by have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num); linarith
  have hsK : (1 : ℝ) ≤ (splitK : ℝ) := by unfold splitK; norm_num
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the unsplit Phase-3 budget
  have hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans ?_ hNC3'
    have h1 : (1 : ℝ) ≤ (splitK : ℝ) * (3 * 5 ^ d) := by nlinarith
    have h2 : max (cAlpha d γ η) (cBeta η c) ≤ (splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h2 hN0
  -- phase 4
  have P4 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv4 M₀ Rn (H.Reach4 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h := by
    refine phase4_cover HR hS hp0 hP hP0 c hnc ?_ N hN4 (fun h => (N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn k hk hr; exact H.hext4 hn k hk hr
    · intro A h h' hA hap hI hs
      exact scale_step (a := 0) (N : ℝ≥0∞) (N : ℝ≥0∞) (hW4 hL1 hη0 hY0 crit _ hK4 N γ hNC4 hap hI hs)
    · intro A h hA hn
      have := hterm A h hA hn
      gcongr
  -- phase 3
  have P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3 M₀ Rn (H.Reach3 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h := by
    refine H.phase3_cover HR hS hp0 hP hP0 c hnc hobl (fun κ h hr => hr.toAny) ?_ h0 h2 N hN3
      (fun h => (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ z b a sg hn hdes k hk hr; exact H.hext3 hn hdes k hk hr
    · intro A h h' hA hap hI hs
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 2) (hW3 hL1 hη0 hY0 crit _ hK3 N hNC3 hap hI hs)
    · intro A h hA hn
      have := P4 h A (hA.toInv4 fun κ hκ hr => hr.to4 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h := by ring
  -- phase 2, with the bank
  have hgl : 0 ≤ ghostConstLow d c η δ := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
  have h9 : (1 : ℝ) ≤ 9 * 25 ^ d := by have : (1 : ℝ) ≤ 25 ^ d := one_le_pow₀ (by norm_num); linarith
  have hgle : 9 * 25 ^ d * ghostConstLow d c η δ ≤ H.ghostConstChain d c η δ := by
    unfold H.ghostConstChain; nlinarith [mul_nonneg hgl (by linarith : (0 : ℝ) ≤ 9 * 25 ^ d)]
  have hNC2 : ((splitK * N : ℕ) : ℝ) * H.ghostConstChain d c η δ ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC2'; push_cast; ring
  have P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3 M₀ Rn (H.Reach2 C Un Fst L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    refine phase2_bank_cover (C := C) HR hS hp0 hP hP0 c hnc (fun κ h hr => hr.toAny) ?_ h0 h2 N hN2
      (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h n hn hdes k hk hr; exact H.hext2 hn hdes k hk hr
    · intro A h h' hA hap hI hs
      have hw := scale_step (a := 0) ((splitK * N : ℕ) : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3)
        (hW2 hL1 hη0 hY0 crit _ hK2 (splitK * N) hNC2 hap hI hs)
      refine le_trans ?_ hw
      exact mul_le_mul' le_rfl (mul_le_mul' (H.ofReal_mul_le_of_le (mul_nonneg (by linarith) hgl) hgle) le_rfl)
    · intro A h hA hn
      have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h := by ring
  -- phase 1, with the bank
  have hNC1 : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max CA CN ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC1'; push_cast; ring
  have hNC3s : ((splitK * N * (3 * 5 ^ d) : ℕ) : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC3'; push_cast; ring
  have hW1 : ∀ (h : HSt V D₀) (t : T1 h), ApPos h.s → Inv Rn h.s → H.Node1 C crit L γ η h t →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * vCost L γ η CA CN h (H.post1 C crit L γ η h t)) *
        ((N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) (H.post1 C crit L γ η h t))) ≤
        (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h := by
    intro h t hap hI hn
    rw [cast_three_five d]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 4)
      (H.hW1_of hL1 hη0 hY0 crit Fmax hCA hCN (splitK * N * (3 * 5 ^ d)) hNC1 hap hI hn)
  have hW3' : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h h' : HSt V D₀), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ApPos h.s →
      Inv Rn h.s → UStep3 L γ η w (fun k => k ∈ A) h h' →
      ((splitK * N : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') *
        ((N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h')) ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h := by
    intro A h h' hA hap hI hs
    have e : (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h' : ℝ) =
        ((3 * 5 ^ d : ℕ) : ℝ) * (max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') := by push_cast; ring
    rw [e]
    refine kn_absorb (splitK * N) (3 * 5 ^ d) _ _ _ ?_
    exact scale_step (a := 0) _ ((N : ℝ≥0∞) ^ 4)
      (hW3_1 hL1 hη0 hY0 crit Fmax _ hγ0 hK3 (splitK * N * (3 * 5 ^ d)) hNC3s hap hI hs)
  have hfin : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) (b : ℕ), H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h →
      bank L γ η w h A ≤ b → (∀ k ∈ A, H.Stuck1 C L γ η w Un k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
        ((N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
    intro A h b hA hb hst
    by_cases hAe : A = ∅
    · subst hAe; simp [QS_empty]
    have hap := (hA.2.resolve_left hAe).2.1
    have hF := hend A h hA hAe hst
    have := P2 h A b (hA.map fun κ hκ hr => hr.to2 (hst κ hκ)) hb
    have hWle : WPot L γ η Y0 (gExp η crit) h ≤ WPot L γ η Y0 (g1 γ η crit Fmax) h := by
      refine WPot_mono hL1 hY0 (apProd_pos hL hap) ?_
      unfold g1
      nlinarith
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * (((N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h) *
          ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) := by gcongr
      _ = ((N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (gExp η crit) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by ring
      _ ≤ ((N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h) * ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
          gcongr

  have key := phase1_bank_cover HR hS hp0 hP hP0 c hnc hExA hExN hExC hν hSrc hdec h0 N hN1
    (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h) hmem hW1 hW3' hfin (HSt.init M₀) A0 0 hInit
    (by rw [bank_init])
  simpa only [Nat.cast_zero, mul_zero, Real.rpow_zero, ENNReal.ofReal_one, mul_one] using key

end WaveTurbulence.GammaLow.FinalCount.Ghost
