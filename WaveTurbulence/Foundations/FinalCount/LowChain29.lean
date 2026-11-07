/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain28
public import WaveTurbulence.Foundations.FinalCount.LowChain15
/-! **FINALCOUNT LOW-CHAIN, LOW-CHAIN session 6 (3): `chain_coverLL`.**  The chain of the five cover theorems of the LOW run (see LowChain15). 
Generalized in the index profile: `Y0f L γ η ε0` replaced by `Yp` (R79 session 6). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The chain of the five cover theorems (LOW run), general index profile.** -/
theorem chain_coverLL [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop}
    {CA CN CD ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν) (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (h8 : 8 * η ≤ 2 * γ - 1) (hη40 : η ≤ 1 / 40)
    (N : ℕ)
    (hN1 : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hN3 : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N)
    {ε0 Fmax : ℝ} (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2) (hCA : 0 ≤ CA) (hCN : 0 ≤ CN) (hCD : 0 ≤ CD)
    (hNC1 : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6))
    (hK2 : 0 ≤ ghostConst d c η δ)
    (hNC2 : (N : ℝ) * ghostConst d c η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hK4 : 0 ≤ cBeta η c)
    (hNC4 : (N : ℝ) * cBeta η c ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hγ0 : 0 ≤ min γ (1 - γ))
    -- named inputs
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1 C L γ η w Un κ h →
      (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) ∨
      (∃ t ∈ nodes1D C crit h, κ ∈ cls1D L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2)
          t.1 t.2.1 t.2.2.1 t.2.2.2))
    (hend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1L M₀ Rn C Un Fst L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (h.s.M.numComponents : ℝ) ≤ Fmax)
    (hterm : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn (Reach4L C Un Fst L γ η w) L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) →
      QS L γ δ C₁ w P h A ≤ WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1L M₀ Rn C Un Fst L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hL0 : 0 < L := by linarith
  have hη0 : 0 ≤ η := H.hη.le
  have hNpos : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hY : ∀ (R : ℕ), 0 ≤ Yp R := hYp0
  -- phase 4
  have P4 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach4L C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine phase4_coverL H hS hp0 hP hP0 c hnc ?_ N hN4
      (fun h => (N : ℝ≥0∞) * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn k hk hr; exact hext4L hn k hk hr
    · intro A h h' R' hA hap hg hne hs
      have e : RofS h'.s = RofS h.s := (rofS_ustep4 hg hs hne).trans (rofS_of_inv hg.1).symm
      have key := hW4 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit _ hK4 N γ hNC4 hap hg.1 hs
      rw [e]
      exact scale_step (a := 0) (N : ℝ≥0∞) (N : ℝ≥0∞) key
    · intro A h hA hn
      have := hterm A h hA hn
      gcongr
  -- phase 3
  have P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach3L C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine phase3_coverL H hS hp0 hP hP0 c hnc hobl (fun κ h hr => hr) ?_ h0 h2 N hN3
      (fun h => (N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ z b a sg hn hdes k hk hr; exact hext3L hn hdes k hk hr
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
  -- phase 2
  have P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (Reach2L C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine phase2_coverL (C := C) H hS hp0 hP hP0 c hnc h8 (fun κ h hr => hr) ?_ h0 h2 N hN2
      (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h n hn hdes k hk hr; exact hext2L hn hdes k hk hr
    · intro A h h' R' hA hap hg hne hs
      have e : RofS h'.s = RofS h.s := (rofS_ustep2 hg hs hne).trans (rofS_of_inv hg.1).symm
      have key := hW2 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit _ hK2 N hNC2 hap hg.1 hs
      rw [e]
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3) key
    · intro A h hA hn
      have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
  -- the Step D3 phase
  have PD3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3L M₀ Rn (ReachD3 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by
    refine phaseD3_coverL (C := C) H hS hp0 ?_ N hN4
      (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn hdes k hk hr; exact hextD3L hn hdes k hk hr
    · intro A h h' R' hA hap hg hne hs
      obtain ⟨k, hk⟩ := hne
      obtain ⟨v, x₁, x₂, hD, rfl⟩ := (hs.hstep hk).data
      have key := hW_D3p (L := L) (γ := γ) (η := η) hL1 hη0 hγ0 ε0 Yp hYp0 hYpd hε0 crit hg hD hap N hND3
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 4) key
    · intro A h hA hn
      have := P2 h A (hA.map fun κ hκ hr => hr.to2 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 3 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
  -- phase 1
  refine phase1_coverL H hS hp0 hP hP0 c hnc hExA hExN hExD hν hSrc hdec h0 N hN1
    (fun h => (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h) hmem ?_ ?_ ?_ ?_
  · intro h t R' hap hg hn
    have e : RofS (post1 C crit L γ η h t).s = RofS h.s := (rofS_post1 hg.1 hn).trans (rofS_of_inv hg.1).symm
    have key := hW1_of hL1 hη0 (hY (RofS h.s)) crit Fmax hCA hCN N hNC1 hap hg.1 hn
    rw [e]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5) key
  · intro h t R' hap hg hn
    obtain ⟨K, F, hK, -⟩ := node1D_spec hn
    have key := hW_D1'p (L := L) (γ := γ) (η := η) hL1 hη0 hη40 hγ0 ε0 Yp hYp0 hYpd hε0 crit Fmax K hg.1 hap F.hu F.hl F.hd2
      (vineCut_F_lt K F.hd2) (vine_atoms_eps hg.1 K F.hu F.hl) F.hint (fun x hx => deg_le_four _ (hg.1.bounds x hx))
      F.hloss hCD N hNCD
    rw [hK]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5) key
  · intro A h h' R' hA hap hg hne hs
    have e : RofS h'.s = RofS h.s := (rofS_ustep3 hg hs hne).trans (rofS_of_inv hg.1).symm
    have key := hW3_1 (Rn := R') hL1 hη0 (hY (RofS h.s)) crit Fmax _ hγ0 hK3 N hNC3 hap hg.1 hs
    rw [e]
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 5) key
  · intro A h hA hst
    by_cases hAe : A = ∅
    · subst hAe; simp [QS_empty]
    have hap := (hA.2.resolve_left hAe).2.1
    have hF := hend A h hA hAe hst
    have := PD3 h A (hA.map fun κ hκ hr => hr.toD3 (hst κ hκ))
    have hWle : WPot L γ η (Yp (RofS h.s)) (gExp η crit) h ≤ WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by
      refine WPot_mono hL1 (hY _) (apProd_pos hL0 hap) ?_
      unfold g1
      nlinarith
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 4 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :=
          by gcongr
      _ = (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (gExp η crit) h := by ring
      _ ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1 γ η crit Fmax) h := by gcongr

end WaveTurbulence.FinalCountAsm
