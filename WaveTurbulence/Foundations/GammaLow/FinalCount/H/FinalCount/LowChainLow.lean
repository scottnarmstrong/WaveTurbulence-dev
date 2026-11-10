/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain29
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChainLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1Cone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # H-LOW (packet L6-HLOW): the low-range `chain_coverLL` (the ghost step of the LOW chain at `γ ≤ 1/2`)

wt-orch RULING R194 (wt-l6ghost's corrected field, H-G3-PROGRESS "GHOST ASSEMBLY"; H-ASM's `ChainCoverLow'` in
`AsmChainLow`): the LOW chain's ghost step enters the low range only through `ChainCoverLowL'`. It is the statement of the
ported `H.chain_coverLL` (LowChain29; main's `FinalCountAsm.chain_coverLL`, binders and conclusion copied by source),
with exactly the changes of `ChainCoverLow'`:
* `h8 : 8 * η ≤ 2 * γ - 1` deleted (it fails for every `γ ≤ 1/2`);
* R194 (1): the conclusion only at the initial state `(HSt.init M₀, A0)`, the consumer's only use
  (`LowChain45.low_loop_class_bound`);
* R194 (2): the Phase-1 cone input `hExC : Ex1Cone … CA` (H-ASM's `AsmEx1Cone`; the LOW run's Phase-1 vine steps are the
  same uniform steps as `Ex1A`'s), with the same `CA` as `hExA`;
* R194 (3), in the form agreed between H-ASM and the prover wt-l6ghost (H-G3-PROGRESS "REQUEST to H-ASM";
  `AsmChainLow`): the (f′) split budget is the constant `Ghost.splitK = 18`, as explicit factors in `hNC1'` (Op-1
  creations, `× 3·5^d`), `hNC2'` (charged Phase-2 steps, constant `ghostConstChain`, also in `hK2`) and `hNC3'`
  (Phase-1 α-cuts, `× 3·5^d`, `Ghost.cut_excess_cone`).
LOW-specific (confirmed by wt-l6ghost, H-G3-PROGRESS "R194 adopted": "your `Ex1D`/`hNCD` binders stay as they are"): the degree-`2` steps of the LOW run (Step D1 `Ex1D` with `hNCD`; Step D3
with `hND3`) are unchanged. Both leave `β`-atoms (`HStepD1`: the surviving halves of the degree-`2` joint; `HStepD3`:
the cut `ε`-atom), so they create no critical α-atom, no ghost and no cone.
Stated at `V D₀ : Type` (its consumer is at `Type`). Its truth is M1-R2 Theorem 6.1 + Theorem 7.1 (root telescoping). It
is the only field of `Src.LowInputs` (`H/InputsLow.lean`); prover: wt-l6ghost. `node2_factsL`, `phase2_coverL`,
`chain_coverLL` with `h8` stay unused for `γ ≤ 1/2`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

/-- **The low-range `chain_coverLL`, root form** (the ghost step of the LOW chain for `γ ≤ 1/2`; RULING R194; see the
module docstring). -/
def ChainCoverLowL' : Prop :=
  ∀ {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
      {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop}
      {CA CN CD ν : ℝ}
      (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
      (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
      (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
      (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
      (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν) (hExD : Ex1D L γ η δ C₁ w M₀ C P CD ν)
      (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
      (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
      (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
      (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
      (h2 : 2 / L ≤ L ^ (-γ + η)) (hη40 : η ≤ 1 / 40)
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
      (hNC1' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max CA CN) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
      (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
      (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6))
      (hK2 : 0 ≤ ghostConstChain d c η δ)
      (hNC2' : (N : ℝ) * ((Ghost.splitK : ℝ) * ghostConstChain d c η δ) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
      (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
      (hNC3' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c)) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
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
        QS L γ δ C₁ w P h A ≤ WPot L γ η (Yp (RofS h.s)) (gExp η crit) h)
      (hInit : Inv1L M₀ Rn C Un Fst L γ η w A0 A0 (HSt.init M₀)),
        QS L γ δ C₁ w P (HSt.init M₀) A0 ≤
          (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS (HSt.init M₀).s)) (g1 γ η crit Fmax) (HSt.init M₀)

end WaveTurbulence.GammaLow.FinalCount.H
