/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1H
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhased
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Leaves
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.ChainSpec
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1Cone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api

/-! # H-ASM (packet L6-HASM): the low-range `chain_cover` (the ghost step at `γ ≤ 1/2`)

wt-orch DECISION (H-ASM-PROGRESS "Ghost step") and RULING R194 (wt-l6ghost's corrected field, H-G3-PROGRESS "GHOST
ASSEMBLY"): the REG chain's ghost step enters the low range only through `ChainCoverLow'`, the statement of main's
`FinalCountAsm.chain_cover` (the ported `H.FinalCount.AsmChain2.chain_cover`, sha256 of the source file 79234299a5793015…,
binders and conclusion copied by source; replacements in `ASM-COPIED-SHA256SUMS`) with exactly these changes:
* `h8 : 8 * η ≤ 2 * γ - 1` deleted (it fails for every `γ ≤ 1/2`);
* R194 (1): the conclusion only at the initial state `(HSt.init M₀, A0)` (the consumer's only use,
  `AsmTopClass3.reg_class_bound`): at intermediate Phase-1 states the creation-cone gain is already spent, so the
  every-state form is not provable (wt-l6ghost's obstruction O1); the class-dependent invariant with the bank
  `L^{5η·pend(h,A)}` is internal to the prover;
* R194 (2): the new Phase-1 input `hExC : Ex1Cone … CA` (`AsmEx1Cone`: the Op-1 creation cone of M1-R2 Thm 6.1 (e),
  produced by `ex1C_uniform` from L6E2's `Ghost.prop94_vine_all_family_cone`), with the same `CA` as `hExA`;
* R194 (3), in the form agreed with the prover wt-l6ghost (H-G3-PROGRESS "REQUEST to H-ASM"): the (f′) split budget
  is the constant `Ghost.splitK = 18` (every node splits into 3·3·2 classes: per new degree-2 critical atom TR to its
  old critical neighbours or a cone around neighbour 1 or 2, plus the TR/related bit of two new atoms), as explicit
  factors: `hNC1' : N · (splitK · (3·5^d) · max CA CN) ≤ L^{η³ − 4η⁶(86+2)}`, `hNC2' : N · (splitK · ghostConstChain)
  ≤ L^{η³ − 4η⁶(9+3)}`, and `hNC3' : N · (splitK · (3·5^d) · max cAlpha cBeta) ≤ L^{η³ − 4η⁶(1+1)}` (Phase-1 α-cuts
  also create critical atoms: split and cone, `Ghost.cut_excess_cone`, M1-R2 §11a);
* the ghost constant `ghostConst d c η δ` of `hK2`, `hNC2'` is `ghostConstChain d c η δ`, the constant of a charged
  Phase-2 step: `≥ Ghost.ghostConstLow` (triangle steps, `Ghost.UStep2.excess_low`), `≥ 9·25^d · ghostConst`
  (creation steps, `Ghost.UStep2.excess_cone`), with a factor `2` for the TR/NC bit;
* stated at `V D₀ : Type` (its consumer is at `Type`).
Its truth is M1-R2 Theorem 6.1 + Theorem 7.1 (root telescoping). It is the only field of `Src.AsmInputs`; prover:
wt-l6ghost. `node2_facts`, `phase2_cover`, `chain_cover` with `h8` stay unused for `γ ≤ 1/2`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the binder names of `ChainCoverLow'` document the statement for its prover
set_option linter.unusedVariables false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

/-- **The constant of a charged Phase-2 step at `γ ≤ 1/2`**: `2 · (ghostConstLow + 1) · 9·25^d`. -/
noncomputable def ghostConstChain (d c : ℕ) (η δ : ℝ) : ℝ :=
  2 * ((Ghost.ghostConstLow d c η δ + 1) * (9 * 25 ^ d))

theorem ghostConstLow_nonneg (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : 0 ≤ Ghost.ghostConstLow d c η δ :=
  ((triConst_nonneg d c hη hδ).trans (ghostConst_ge_triConst d c hη hδ)).trans (Ghost.ghostConst_le_low d c hδ)

theorem ghostConstChain_nonneg (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) : 0 ≤ ghostConstChain d c η δ := by
  have := ghostConstLow_nonneg d c hη hδ
  unfold ghostConstChain; positivity

theorem ghostConstLow_le_chain (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    Ghost.ghostConstLow d c η δ ≤ ghostConstChain d c η δ := by
  have h0 := ghostConstLow_nonneg d c hη hδ
  have h1 : (1 : ℝ) ≤ 9 * 25 ^ d := by have : (1 : ℝ) ≤ 25 ^ d := one_le_pow₀ (by norm_num); linarith
  unfold ghostConstChain; nlinarith

theorem cone_le_chain (d c : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    9 * 25 ^ d * ghostConst d c η δ ≤ ghostConstChain d c η δ := by
  have h0 := ghostConstLow_nonneg d c hη hδ
  have hg := Ghost.ghostConst_le_low d c (η := η) hδ
  have h1 : (0 : ℝ) ≤ 9 * 25 ^ d := by positivity
  unfold ghostConstChain; nlinarith

/-- **The low-range `chain_cover`, root form** (the ghost step of the REG chain for `γ ≤ 1/2`; RULING R194; see the
module docstring). -/
def ChainCoverLow' : Prop :=
  ∀ {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} {L γ η δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ}
      {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit : V → Prop} {CA CN ν : ℝ}
      (H : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
      (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
      (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
      (hobl : ∀ κ ∈ A0, SubproOblG C L γ η w κ)
      (hExA : Ex1A L γ η δ C₁ w M₀ P CA) (hExN : Ex1N L γ η δ C₁ w M₀ P CN ν)
        (hExC : Ex1Cone L γ η δ C₁ w M₀ P CA)
      (hν : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ ν) (hSrc : ∀ k ∈ A0, SourceLadderGaps M₀ L w P k)
      (hdec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L w c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0)
      (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
      (h2 : 2 / L ≤ L ^ (-γ + η))
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
      (hNC1' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max CA CN) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))))
      (hK2 : 0 ≤ ghostConstChain d c η δ)
      (hNC2' : (N : ℝ) * ((Ghost.splitK : ℝ) * ghostConstChain d c η δ) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))))
      (hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η c))
      (hNC3' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η c)) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))))
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
        QS L γ δ C₁ w P h A ≤ WPot L γ η Y0 (gExp η crit) h),
      Inv1 M₀ Rn C Un Fst L γ η w A0 A0 (HSt.init M₀) →
        QS L γ δ C₁ w P (HSt.init M₀) A0 ≤ (N : ℝ≥0∞) ^ 4 * WPot L γ η Y0 (g1 γ η crit Fmax) (HSt.init M₀)

end WaveTurbulence.GammaLow.FinalCount.H
