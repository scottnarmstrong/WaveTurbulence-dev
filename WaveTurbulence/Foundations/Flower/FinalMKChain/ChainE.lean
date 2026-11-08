/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Chain

/-! # C1b2 MK-CHAIN (5): `chain_coverLLE`, the five covers with survivors

Main's `chain_coverLL` (LowChain29) for the survivor run: C1b1's phase-1 cover `phase1_coverLE_of_inputs` (potential
`g1E`, coverage discharged from the `LowLoopClassHypsMK` fields) with its `hfin` from Chain (`hfinE_of_PD3` over
`PD3E`, `P2E`, `P3E`, `P4E`). The named inputs are main's: the end bound `hend` (C1b1's `hendAtLE_inv1`) and the
terminal bound `hterm` on `Reach4LE` (Term). The hinge pairs of phase 3 come from `SubproOblGMK.hingeSG`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- **The chain of the five cover theorems with survivors** (main's `chain_coverLL`, LowChain29). -/
theorem chain_coverLLE [Infinite V] {M₀ : Molecule V D₀} {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExD : Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν) (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (h8 : 8 * η ≤ 2 * γ - 1) (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hηγ : η ≤ γ) (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Object M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, CollectedF C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → HingeData C.toCollData U)
    (hsh : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hHC : HostConnMK M₀ C Un E L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hobl : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (hshape : ∀ i, ObjVine M₀ (E i))
    (hcritE : ∀ i, ∀ a ∈ (E i).atoms, a ≠ (E i).upper → a ≠ (E i).lower → ¬ crit a)
    (N : ℕ)
    (hN : (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))))) +
      (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
        ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) +
      Fintype.card D₀ * (Fintype.card D₀ * (Fintype.card D₀ * Fintype.card D₀)) + 1 ≤ N)
    {ε0 Fmax : ℝ} (Yp : ℕ → ℝ) (hYp0 : ∀ R, 0 ≤ Yp R)
    (hYpd : ∀ R R' j : ℕ, R' + j = R → Yp R' * L ^ (eraseA γ η * (j : ℝ) - ε0) ≤ Yp R) (hε0 : ε0 ≤ η ^ 2 / 2)
    (hCA : 0 ≤ CA) (hCN : 0 ≤ CN) (hCD : 0 ≤ CD) (hCR : 0 ≤ CR)
    (hNC1 : (N : ℝ) * max CA CN ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCR : (N : ℝ) * CR ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η c) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hN3 : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N)
    (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6))
    (hK2 : 0 ≤ ghostConst d c η δ)
    (hNC2 : (N : ℝ) * ghostConst d c η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (hK4 : 0 ≤ cBeta η c)
    (hNC4 : (N : ℝ) * cBeta η c ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) → (h.s.M.numComponents : ℝ) ≤ Fmax)
    (hterm : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η w) L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) →
      QS L γ δ C₁ w P h A ≤ WPot L γ η (Yp (RofS h.s)) (gExp η crit) h) :
    ∀ (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h →
      QS L γ δ C₁ w P h A ≤ (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS h.s)) (g1E γ η crit Fmax E) h := by
  have hH : ∀ κ ∈ A0, HingeSG C.toCollData L γ η w κ := fun κ hκ => SubproOblGMK.hingeSGP (hobl κ hκ)
  have P4 := P4E (Un := Un) (Fst := Fst) (E := E) (crit := crit) H hS hp0 hP hP0 c hnc N Yp hYp0 hN4 hK4 hNC4 hterm
  have P3 := P3E H hS hp0 hP hP0 c hnc N Yp hYp0 hH h0 h2 hN3 hK3 hNC3 P4
  have P2 := P2E H hS hp0 hP hP0 c hnc N Yp hYp0 h0 h2 h8 hN2 hK2 hNC2 P3
  have PD3 := PD3E H hS hp0 N Yp hYp0 hN4 hYpd hε0 hND3 hγ0 P2
  exact phase1_coverLE_of_inputs H hS hp0 hP hP0 c hnc hExA hExN hExD hExR hν hSrc hdec h0 h8 hη40 hγ0 h2 hηγ hmate
    hdisj hFst hsgC hdesC hsh hHC hcrit hsd hobl hchain hshape hcritE N hN Yp hYp0 hYpd hε0 hCA hCN hCD hCR hNC1 hNCD hNCR
    hK3 hNC3 (hfinE_of_PD3 H N Yp hYp0 hend hγ0 PD3)

end WaveTurbulence.Flower.FinalMKChain
