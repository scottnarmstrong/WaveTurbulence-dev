/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKChain.Reach
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.FinalMKPhase1.Rel
public import WaveTurbulence.Foundations.GammaLow.Flower.FinalMK.H2.Bank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmChainLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1Cone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainSpec

/-! # L8-H2: the low-range `chain_coverLLE` (the ghost step of the marked LOW chain at `γ ≤ 1/2`)

wt-orch RULING R194 (the root form; H-ASM's `H.ChainCoverLow'`, H-LOW's `H.ChainCoverLowL'`): the marked run's ghost
step enters the low range only through `ChainCoverLowLE'`, H2's single named input (H2-PLAN §2). It is the statement of
main's `Flower.FinalMKChain.ChainE.chain_coverLLE` (binders and conclusion copied by source, ported by `h2port.py` onto
L6's low run over `Src.γL`), with exactly these changes:
* `h8 : 8 * η ≤ 2 * γ - 1` deleted (false for every `γ ≤ 1/2`);
* R194 (1): the conclusion only at the initial state `(HSt.init M₀, A0)`, with the hypothesis
  `hInit : Inv1LE … A0 A0 (HSt.init M₀)` — the consumer's only use (`FinalMKChain.Top.low_loop_class_boundMK`);
* R194 (2): the Phase-1 cone input `hExC : H.Ex1Cone … CA` (H-ASM's `AsmEx1Cone`), same `CA` as `hExA`, after `hExR`;
* R194 (3), the agreed form (`Ghost.splitK = 18`): `hNC1'` (Op-1 creations, `× 3·5^d`), `hK2`/`hNC2'` (charged
  Phase-2 steps, constant `H.ghostConstChain`), `hNC3'` (Phase-1 α-cuts, `× 3·5^d`);
  the degree-2 and re-cut steps keep main's budgets `hNCD`, `hNCR`, `hND3` (their fresh atoms are β: no critical α
  atom, no ghost, no cone — L6E2's recipe item 2 for re-cuts, H-LOW's ruling for Step D1/D3);
* the re-cut bank `L^{3/2}` (H2-PLAN §0 change 2, FINDINGS F1, APPROVED): the potential is `g1E32` (`H2/Bank.lean`)
  in place of main's `g1E`.
Stated at `V D₀ : Type` (its consumer is at `Type`). Its truth: M1-R2 Thm 6.1 + Thm 7.1 (root telescoping),
REF-M1R2 R1, O75 §11.3 (Operation 1E), REF-M3 R3 with F1. Prover: wt-l6ghost (`Ghost/ChainLowLE.lean`). It is the only
field of `MKLowInputs`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.Flower.H2
open WaveTurbulence.GammaLow.FinalCount WaveTurbulence.GammaLow.Flower
open WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.Flower.FinalMKPhase1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

/-- **The low-range `chain_coverLLE`, root form** (the ghost step of the marked LOW chain for `γ ≤ 1/2`; RULING R194;
see the module docstring). -/
def ChainCoverLowLE' : Prop :=
  ∀ {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} [Infinite V] {M₀ : Molecule V D₀}
    {m Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d}
    {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {E : Fin m → Src.Object Src.γL M₀} {crit : V → Prop} {CA CN CD CR ν : ℝ}
    (H : TriReal d L γ η δ C₁) (hS : SubHypL Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (hExA : FinalCount.H.Ex1A L γ η δ C₁ w M₀ P CA) (hExN : FinalCount.H.Ex1N L γ η δ C₁ w M₀ P CN ν)
    (hExD : FinalCount.H.Ex1D L γ η δ C₁ w M₀ C.toCollData P CD ν) (hExR : Ex1RC L γ η δ C₁ w M₀ C.toCollData P CR ν)
    (hExC : FinalCount.H.Ex1Cone L γ η δ C₁ w M₀ P CA)
    (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
    (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hη40 : η ≤ 1 / 40) (hγ0 : 0 ≤ min γ (1 - γ)) (h2 : 2 / L ≤ L ^ (-γ + η))
    (hηγ : η ≤ γ) (hmate : ∀ κ ∈ A0, ∀ x, κ (M₀.mate x) = κ x)
    (hdisj : ∀ κ ∈ A0, ∀ U U' : Src.Object Src.γL M₀, CollectedF C (Un κ) L γ η w κ U → CollectedF C (Un κ) L γ η w κ U' →
      FinalCount.H.SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    (hFst : ∀ κ ∈ A0, ∀ U ∈ Fst, CollectedF C (Un κ) L γ η w κ U)
    (hsgC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.HasGapKind L γ η w κ .SG)
    (hdesC : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → FinalCount.H.HingeData C.toCollData U)
    (hsh : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → U.atoms.card = 3 ∨ FinalCount.H.ObjVine M₀ U)
    (hHC : HostConnMK M₀ C Un E L γ η w A0)
    (hcrit : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a)
    (hsd : ∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hobl : ∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (hshape : ∀ i, FinalCount.H.ObjVine M₀ (E i))
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
    (hNC1' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max CA CN) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCD : (N : ℝ) * CD ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hNCR : (N : ℝ) * CR ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
    (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
    (hNC3' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c)) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hN2 : nodeBound2 (2 * M₀.atoms.card) (Fintype.card D₀) ⌈2 * Real.log L⌉₊ + 1 ≤ N)
    (hN3 : (2 * M₀.atoms.card) * (Fintype.card D₀ * (Fintype.card D₀ *
      ((⌈2 * Real.log L⌉₊ + 1) * (2 * ((2 * M₀.atoms.card) * 2))))) + 1 ≤ N)
    (hN4 : 2 * M₀.atoms.card * Fintype.card D₀ * Fintype.card D₀ + 1 ≤ N)
    (hND3 : (N : ℝ) ≤ L ^ (η ^ 3 - 4 * η ^ 6))
    (hK2 : 0 ≤ FinalCount.H.ghostConstChain d c η δ)
    (hNC2' : (N : ℝ) * ((Ghost.splitK : ℝ) * FinalCount.H.ghostConstChain d c η δ) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
    (hK4 : 0 ≤ cBeta η c)
    (hNC4 : (N : ℝ) * cBeta η c ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
    (hend : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv1LE M₀ Rn C Un Fst E L γ η w A0 A h → A ≠ ∅ →
      (∀ k ∈ A, Stuck1E C L γ η w Un E k h) → (h.s.M.numComponents : ℝ) ≤ Fmax)
    (hterm : ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η w) L w A0 A h →
      (∀ k ∈ A, NoBetaCut L w k h.s) →
      QS L γ δ C₁ w P h A ≤ WPot L γ η (Yp (RofS h.s)) (gExp η crit) h)
    (hInit : Inv1LE M₀ Rn C Un Fst E L γ η w A0 A0 (HSt.init M₀)),
      QS L γ δ C₁ w P (HSt.init M₀) A0 ≤
        (N : ℝ≥0∞) ^ 5 * WPot L γ η (Yp (RofS (HSt.init M₀).s)) (g1E32 γ η crit Fmax E) (HSt.init M₀)

/-- **The named inputs of L8-H2** (a `Prop` class, as L6's `Src.LowInputs`): its only field is the marked chain
cover's root form. Prover: wt-l6ghost; H2 discharges the class by an instance once the proof is published. -/
class MKLowInputs : Prop where
  /-- The low-range root form of `chain_coverLLE` (RULING R194, bank `3/2`). -/
  chainCoverLE : ChainCoverLowLE'

end WaveTurbulence.GammaLow.Flower.H2
