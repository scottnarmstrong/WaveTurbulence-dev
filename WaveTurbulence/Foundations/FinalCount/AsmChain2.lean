/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmChain
/-! **FINALCOUNT-ASSEMBLY: `chain_cover`** -/
@[expose] public section
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

/-- `W` is antitone in the exponent. -/
theorem WPot_mono {L γ η : ℝ} (hL1 : 1 ≤ L) {Y0 : ℝ} (hY0 : 0 ≤ Y0) {g g' : HSt V D₀ → ℝ} {h : HSt V D₀}
    (hap : 0 < apProd L γ η h.s) (hg : g' h ≤ g h) : WPot L γ η Y0 g h ≤ WPot L γ η Y0 g' h := by
  unfold WPot potR
  refine ENNReal.ofReal_le_ofReal ?_
  have hL : 0 < L := by linarith
  have h1 : L ^ (-g h) ≤ L ^ (-g' h) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2 : 0 ≤ L ^ (-(2 * min γ (1 - γ) + 5 * η ^ 2) * (h.s.M.numComponents : ℝ) +
      (min γ (1 - γ) + 2 * η ^ 2) * (vBeta h.s : ℝ)) := by positivity
  apply div_le_div_of_nonneg_right _ hap.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hY0) h2

/-- **The chain of the four cover theorems.** -/
theorem chain_cover [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
    {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {CA CN ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h2 : 2 / L ≤ L ^ (-γ + η)) (h8 : 8 * η ≤ 2 * γ - 1)
    (N : ℕ)
    (hN1 : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hN3 : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N)
    {Y0 Fmax : ℝ} (hY0 : 0 ≤ Y0) (hCA : 0 ≤ CA) (hCN : 0 ≤ CN)
    (hNC1 : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hK2 : 0 ≤ ghostConst d c η δ)
    (hNC2 : (N : ℝ) * ghostConst d c η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hK4 : 0 ≤ cBeta η c)
    (hNC4 : (N : ℝ) * cBeta η c ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hγ0 : 0 ≤ min γ (1 - γ))
    -- named inputs
    (hmem : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → ∀ κ ∈ A,
      ¬ Stuck1 C L γ η w Un κ h →
      (∃ t ∈ nodes1 C crit L γ η h, κ ∈ cls1 L γ η w h (Avine C Un Fst L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
          t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2) ∨
      (∃ t ∈ nodesT C L γ η h, κ ∈ cls3 L γ η w h (Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2))
    (hend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1 M₀ Rn C Un Fst L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1 C L γ η w Un k h) → (h.s.M.numComponents : ℝ) ≤ Fmax)
    (hterm : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv4 M₀ Rn (Reach4 C Un Fst L γ η w) L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) →
      QS L γ δ C₁ w P h A ≤ WPot L γ η Y0 (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1 M₀ Rn C Un Fst L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) H.hL
  have hη0 : 0 ≤ η := H.hη.le
  have hNpos : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  -- phase 4
  have P4 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv4 M₀ Rn (Reach4 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h := by
    refine phase4_cover H hS hp0 hP hP0 c hnc ?_ N hN4 (fun h => (N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ hn k hk hr; exact hext4 hn k hk hr
    · intro A h h' hA hap hI hs
      exact scale_step (a := 0) (N : ℝ≥0∞) (N : ℝ≥0∞) (hW4 hL1 hη0 hY0 crit _ hK4 N γ hNC4 hap hI hs)
    · intro A h hA hn
      have := hterm A h hA hn
      gcongr
  -- phase 3
  have P3 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3 M₀ Rn (Reach3 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h := by
    refine phase3_cover H hS hp0 hP hP0 c hnc hobl (fun κ h hr => hr.toAny) ?_ h0 h2 N hN3
      (fun h => (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h v x₁ x₂ z b a sg hn hdes k hk hr; exact hext3 hn hdes k hk hr
    · intro A h h' hA hap hI hs
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 2) (hW3 hL1 hη0 hY0 crit _ hK3 N hNC3 hap hI hs)
    · intro A h hA hn
      have := P4 h A (hA.toInv4 fun κ hκ hr => hr.to4 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) * WPot L γ η Y0 (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h := by ring
  -- phase 2
  have P2 : ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv3 M₀ Rn (Reach2 C Un Fst L γ η w) L w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h := by
    refine phase2_cover (C := C) H hS hp0 hP hP0 c hnc h8 (fun κ h hr => hr.toAny) ?_ h0 h2 N hN2
      (fun h => (N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h) ?_ ?_
    · intro A h n hn hdes k hk hr; exact hext2 hn hdes k hk hr
    · intro A h h' hA hap hI hs
      exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 3) (hW2 hL1 hη0 hY0 crit _ hK2 N hNC2 hap hI hs)
    · intro A h hA hn
      have := P3 h A (hA.map fun κ hκ hr => hr.to3 (hn κ hκ))
      calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2 * WPot L γ η Y0 (gExp η crit) h) :=
            by gcongr
        _ = (N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h := by ring
  -- phase 1
  refine phase1_cover H hS hp0 hP hP0 c hnc hExA hExN hν hSrc hdec h0 N hN1
    (fun h => (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h) hmem ?_ ?_ ?_
  · intro h t hap hI hn
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 4) (hW1_of hL1 hη0 hY0 crit Fmax hCA hCN N hNC1 hap hI hn)
  · intro A h h' hA hap hI hs
    exact scale_step (a := 0) (N : ℝ≥0∞) ((N : ℝ≥0∞) ^ 4) (hW3_1 hL1 hη0 hY0 crit Fmax _ hγ0 hK3 N hNC3 hap hI hs)
  · intro A h hA hst
    by_cases hAe : A = ∅
    · subst hAe; simp [QS_empty]
    have hap := (hA.2.resolve_left hAe).2.1
    have hF := hend A h hA hAe hst
    have := P2 h A (hA.map fun κ hκ hr => hr.to2 (hst κ hκ))
    have hL : 0 < L := by linarith
    have hWle : WPot L γ η Y0 (gExp η crit) h ≤ WPot L γ η Y0 (g1 γ η crit Fmax) h := by
      refine WPot_mono hL1 hY0 (apProd_pos hL hap) ?_
      unfold g1
      nlinarith
    calc (N : ℝ≥0∞) * QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 3 * WPot L γ η Y0 (gExp η crit) h) :=
          by gcongr
      _ = (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (gExp η crit) h := by ring
      _ ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) h := by gcongr

end WaveTurbulence.FinalCountAsm
