/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Ghost.P2Bank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.LowC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain29
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKChain.Ph3
/-! **Ghost assembly for L8-H2 (C): the marked Phase 2 and Step D3 phase with the bank** (wt-l6ghost).

`P2bankE`: Phase 2 on L8-H2's `Reach2LE` with the bank (`phase2_bank_coverG` with `Reach2LE.rfacts`, `hext2LE`; potential
step main's `hW2` at `splitK·N` with the constant `ghostConstChain ≥ 9·25^d·ghostConstLow`), from Phase 3 (`P3`, e.g.
L8-H2's `P3E`). `PD3bankE`: the Step D3 phase on `ReachD3E` with the bank (`phaseD3_bank_coverL`, `hextD3LE`, main's
`hW_D3p`), from `P2bankE`. These are the bank versions of main's `P2E`, `PD3E` (FinalMKChain/Chain), without `h8`. -/
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

variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **Phase 2 on `Reach2LE` with the bank.** -/
theorem P2bankE [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {E : Fin m → Src.Object Src.γL M₀} {crit : V → Prop}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η))
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hK2 : 0 ≤ FinalCount.H.ghostConstChain d c η δ)
    (hNC2' : (N : ℝ) * ((splitK : ℝ) * FinalCount.H.ghostConstChain d c η δ) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach3LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3L M₀ Rn (Reach2LE C Un Fst E L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hη0 : 0 ≤ η := HR.hη.le
  have hgl : 0 ≤ ghostConstLow d c η δ := ghostConstLow_nonneg (d := d) (c := c) HR.hη HR.hδ0
  have h9 : (1 : ℝ) ≤ 9 * 25 ^ d := by have : (1 : ℝ) ≤ 25 ^ d := one_le_pow₀ (by norm_num); linarith
  have hgle : 9 * 25 ^ d * ghostConstLow d c η δ ≤ FinalCount.H.ghostConstChain d c η δ := by
    unfold FinalCount.H.ghostConstChain; nlinarith [mul_nonneg hgl (by linarith : (0 : ℝ) ≤ 9 * 25 ^ d)]
  have hNC2 : ((splitK * N : ℕ) : ℝ) * FinalCount.H.ghostConstChain d c η δ ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) := by
    refine le_trans (le_of_eq ?_) hNC2'; push_cast; ring
  refine phase2_bank_coverG (C := C.toCollData) HR hS hp0 hP hP0 c hnc (fun κ hκ h hr => hr.rfacts hS (h0 κ hκ)) ?_
    h0 h2 N hN2 (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h n hn hdes k hk hr; exact hext2LE hn hdes k hk hr
  · intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep2 hg hs hne).trans (rofS_of_inv hg.1).symm
    have key := hW2 (Rn := R') hL1 hη0 (hYp0 (RofS h.s)) crit _ hK2 (splitK * N) hNC2 hap hg.1 hs
    rw [e]
    have hw := scale_step (a := 0) ((splitK * N : ℕ) : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3) key
    refine le_trans ?_ hw
    exact mul_le_mul' le_rfl (mul_le_mul' (FinalCount.H.ofReal_mul_le_of_le (mul_nonneg (by linarith) hgl) hgle) le_rfl)
  · intro A h hA hn
    have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
          (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) := by gcongr
      _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring

/-- **The Step D3 phase on `ReachD3E` with the bank.** -/
theorem PD3bankE [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {E : Fin m → Src.Object Src.γL M₀} {crit : V → Prop}
    (HR : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N) {ε0 : ℝ}
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6)) (hγ0 : 0 ≤ min γ (1 - γ))
    (P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3L M₀ Rn (Reach2LE C Un Fst E L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ)))) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (b : ℕ),
      Inv3L M₀ Rn (ReachD3E C Un Fst E L γ η w) L w A0 A h → bank L γ η w h A ≤ b →
      QS L γ δ C₁ w P h A ≤ ((N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) *
        ENNReal.ofReal (L ^ (5 * η * (b : ℝ))) := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) HR.hL
  have hη0 : 0 ≤ η := HR.hη.le
  refine phaseD3_bank_coverL (C := C.toCollData) HR hS hp0 ?_ N hN4
    (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h v x₁ x₂ hn hdes k hk hr; exact hextD3LE hn hdes k hk hr
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

end WaveTurbulence.GammaLow.Flower.H2.Ghost
