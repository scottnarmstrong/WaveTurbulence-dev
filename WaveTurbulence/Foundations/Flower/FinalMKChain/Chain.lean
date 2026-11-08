/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Ph2
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov6
public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.End2
public import WaveTurbulence.Foundations.FinalCount.LowChain29

/-! # C1b2 MK-CHAIN (4): the chain of the five cover theorems with survivors (`chain_coverLLE`)

Copy-thread of main's LowChain29 (`chain_coverLL`). Phase 1 is C1b1's `phase1_coverLE_of_inputs` (survivor Step 1,
potential `g1E`); its one remaining input `hfin` (the end of Step 1, phases D3/2–4) is proved here (`hfinE`):
- phases 4 and D3 are main's generic covers (`phase4_coverL`, `phaseD3_coverL`) on `Reach4LE`/`ReachD3E`;
- phases 3 and 2 are `phase3_coverG`/`phase2_coverG` (Ph3/Ph2) with `HingeSG` and `RFacts`;
- at a `Stuck1E` state no re-cut is pending (`pendRC_zero_of_stuck`), so `g1E = g1` there
  (`WPot_g1E_of_pend_zero`), and `gExp ≤ g1` from `F ≤ Fmax` (`hend`, C1b1's `hendAtLE_inv1` with
  `Fmax = 2R − 1 + m`). -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Phase 4 and the terminal bound on `Reach4LE` (main's `chain_coverLL`, phase 4). -/
theorem P4E [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N)
    (hK4 : 0 ≤ cBeta η c)
    (hNC4 : (N : ℝ) * cBeta η c ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hterm : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η w) L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) →
      QS L γ δ C₁ w P h A ≤ WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  refine phase4_coverL H hS hp0 hP hP0 c hnc ?_ N hN4
    (fun h => (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h v x₁ x₂ hn k hk hr; exact hext4LE hn k hk hr
  · intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep4 hg hs hne).trans (rofS_of_inv hg.1).symm
    have key := hW4 (Rn := R') hL1 hη0 (hYp0 (RofS h.s)) crit _ hK4 N γ hNC4 hap hg.1 hs
    rw [e]
    exact scale_step (a := 0) (N : ℝ≥0∞) (N : ℝ≥0∞) key
  · intro A h hA hn
    have := hterm A h hA hn
    gcongr

/-- Phase 3 on `Reach3LE` (main's `chain_coverLL`, phase 3). -/
theorem P3E [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hH : ∀ κ ∈ A0, HingeSG C.toCollData L γ η w κ)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η))
    (hN3 : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (P4 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach3LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  refine phase3_coverG H hS hp0 hP hP0 c hnc hH (fun κ hκ h hr => hr.rfacts hS (h0 κ hκ)) ?_ h2 N hN3
    (fun h => (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h v x₁ x₂ z b a sg hn hdes k hk hr; exact hext3LE hn hdes k hk hr
  · intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep3 hg hs hne).trans (rofS_of_inv hg.1).symm
    have key := hW3 (Rn := R') hL1 hη0 (hYp0 (RofS h.s)) crit _ hK3 N hNC3 hap hg.1 hs
    rw [e]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 2) key
  · intro A h hA hn
    have := P4 h A (hA.map fun κ hκ hr => hr.to4 (hn κ hκ))
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
          by gcongr
      _ = (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring

/-- Phase 2 on `Reach2LE` (main's `chain_coverLL`, phase 2). -/
theorem P2E [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (h8 : 8 * η ≤ 2 * γ - 1)
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hK2 : 0 ≤ ghostConst d c η δ)
    (hNC2 : (N : ℝ) * ghostConst d c η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach3LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach2LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  refine phase2_coverG (C := C.toCollData) H hS hp0 hP hP0 c hnc h8 (fun κ hκ h hr => hr.rfacts hS (h0 κ hκ)) ?_ h2 N
    hN2 (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h n hn hdes k hk hr; exact hext2LE hn hdes k hk hr
  · intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep2 hg hs hne).trans (rofS_of_inv hg.1).symm
    have key := hW2 (Rn := R') hL1 hη0 (hYp0 (RofS h.s)) crit _ hK2 N hNC2 hap hg.1 hs
    rw [e]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3) key
  · intro A h hA hn
    have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
          (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) := by gcongr
      _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring

/-- The Step D3 phase on `ReachD3E` (main's `chain_coverLL`, phase D3). -/
theorem PD3E [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N) {ε0 : ℝ}
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6)) (hγ0 : 0 ≤ min γ (1 - γ))
    (P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach2LE C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (ReachD3E C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  refine phaseD3_coverL (C := C.toCollData) H hS hp0 ?_ N hN4
    (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
  · intro A h v x₁ x₂ hn hdes k hk hr; exact hextD3LE hn hdes k hk hr
  · intro A h h' R' hA hap hg hne hs
    obtain ⟨k, hk⟩ := hne
    obtain ⟨v, x₁, x₂, hD, rfl⟩ := (hs.hstep hk).data
    have key := hW_D3p (L := L) (γ := γ) (η := η) hL1 hη0 hγ0 ε0 Yp hYp0 hYpd hε0 crit hg hD hap N hND3
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 4) key
  · intro A h hA hn
    have := P2 h A (hA.map fun κ hκ hr => hr.to2 (hn κ hκ))
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤
          (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) := by gcongr
      _ = (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring

/-- **The end of Step 1 with survivors** (`hfin` of C1b1's `phase1_coverLE_of_inputs`), from the D3 cover `PD3` and
the end bound `hend`: at a `Stuck1E` state no re-cut is pending, so `g1E = g1 ≤ gExp`. -/
theorem hfinE_of_PD3 [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop}
    (H : TriReal d L γ η δ C₁) (N : ℕ) (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    {Fmax : ℝ}
    (hend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) → (h.s.M.numComponents : ℝ) ≤ Fmax)
    (hγ0 : 0 ≤ min γ (1 - γ))
    (PD3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (ReachD3E C Un Fst E L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) →
      (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hL0 : 0 < L := by linarith
  intro A h hA hst
  by_cases hAe : A = ∅
  · subst hAe; simp [QS_empty]
  have hap := (hA.2.resolve_left hAe).2.1
  have hF := hend A h hA hAe hst
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hAe
  have hst' : Stuck1E C L γ η w Un E κ h := hst κ hκ
  -- `pendRC_zero_of_stuck` (C1b1, Cov6), inlined: its application elaborates slowly here
  have hpend : pendRC E h = 0 := by
    unfold pendRC
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact hi.1 (hst'.2.2 i)
  have hD3 : Inv3L M₀ Rn (ReachD3E C Un Fst E L γ η w) L w A0 A h :=
    Inv3L.map hA fun κ hκ (hr : Reach1LE C Un Fst E L γ η w κ h) => Reach1LE.toD3 hr (hst κ hκ)
  have := PD3 h A hD3
  have hg : g1 γ η crit Fmax h ≤ gExp η crit h := by
    unfold g1
    have : 0 ≤ min γ (1 - γ) * (Fmax - (h.s.M.numComponents : ℝ)) := mul_nonneg hγ0 (by linarith)
    linarith
  have hWle : WPot L γ η (Yp (RofS h.s)) (gExp η crit) h ≤ WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
    rw [WPot_g1E_of_pend_zero _ crit Fmax E hpend]
    exact WPot_mono hL1 (hYp0 _) (apProd_pos hL0 hap) hg
  calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
        by gcongr
    _ = (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
    _ ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by gcongr

end WaveTurbulence.Flower.FinalMKChain
