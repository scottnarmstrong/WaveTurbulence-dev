/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenUnloopMain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowGardenUnloop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Transport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.VineLocalDartObjects
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowGardenUnloopMain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (LOW-GARDEN, session 2): the class transport `lowClassHyps2_unloop`.** 

**Low-range change (L6-HDS).** The ordinary members of `C₂` are one or two double bonds or T-vines (`vc2`, TARGET
`subsetvc`′; main: a vine (V)); the T-vine is transported to the loop-free restriction by `DS.gEmb_isTVine_iff`.
-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

section main
variable {V : Type} [DecidableEq V] [Infinite V] {D : Type} [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The `M`-level data of the loop transport** (all of it holds on the molecule of a garden with loops: it is what the REG producers
supply, stated for the `C₁ ∪ C₂` collected objects, together with `SubHypLoop` and the `ε`-support `heq`). -/
structure LowLoopData (M : Molecule V D) (R : ℕ) (Adm : (D → Fin d → ℤ) → Prop) (P0 : Finset V → ℝ) (C : CollData M)
    (Un : (D → Fin d → ℤ) → Set (Src.Object Src.γL M)) (Fst : Set (Src.Object Src.γL M)) (crit : V → Prop) (kFix : Finset (Mom d))
    (L γ η : ℝ) (m : ℕ) : Prop where
  hSL : SubHypLoop R M
  hmate : ∀ κ, Adm κ → ∀ x, κ (M.mate x) = κ x
  heq : ∀ κ, Adm κ → ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y
  hdec : ∀ κ, Adm κ → ∃ c0, M.IsDecoration L (0 : Mom d) c0 κ ∧ ∀ x ∈ M.atoms, M.deg x = 4 → c0 x = 0
  h0 : ∀ κ, Adm κ → ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  pin : PinnedM0 (fun k => Adm k) L (0 : Mom d) M
  hP0 : ∀ S ∈ M.maximalLadders, 0 ≤ P0 S
  gaps : ∀ κ, Adm κ → SourceLadderGaps M L (0 : Mom d) P0 κ
  hH : HingeNoLoop C
  trip : TripleDesig C
  obl : ∀ κ, Adm κ → SubproOblG C L γ η (0 : Mom d) κ
  unsel : ∀ κ, Adm κ → C.UnselOK L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ, Adm κ → DegenSGT M L γ η (0 : Mom d) κ (fun a => M.IsTame L (0 : Mom d) kFix κ a)
  critSG : ∀ κ, Adm κ → ∀ a, crit a → SGat M L γ η (0 : Mom d) κ a
  card : ((2 * M.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  sg2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → U.HasGapKind L γ η (0 : Mom d) κ .SG
  des2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → HingeData C U
  shape2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → U.atoms.card = 3 ∨ ObjVine M U
  crit2 : ∀ κ, Adm κ → ∀ U, Coll2 C (Un κ) L γ η (0 : Mom d) κ U → ∀ a ∈ U.atoms, a ≠ U.upper → a ≠ U.lower → ¬ crit a
  hC1 : ∀ i j, i ≠ j → Disjoint (C.collection i).atoms (C.collection j).atoms
  hC12 : ∀ κ, Adm κ → ∀ U ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), ∀ i, Disjoint U.atoms (C.collection i).atoms
  hC22 : ∀ κ, Adm κ → ∀ O ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), ∀ O' ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ),
    O.atoms = O'.atoms ∨ Disjoint O.atoms O'.atoms
  vc2 : ∀ κ, Adm κ → ∀ O ∈ C.C2Of L γ η (0 : Mom d) κ (Un κ), (∃ h, O.shape = .vc h) →
    Vine.DoubleChain M O.atoms O.upper O.lower 1 ∨ Vine.DoubleChain M O.atoms O.upper O.lower 2 ∨
      M.IsTVine O.atoms O.upper O.lower
  hC13 : ∀ i, (C.collection i).atoms.card ≠ 3
  hFst : ∀ U ∈ Fst, ∃ i, U = C.collection i
  hFstC : ∀ i, (∃ h, (C.collection i).shape = .vc h) → C.collection i ∈ Fst
  cn : CnBound M C Un Fst L γ η (0 : Mom d) {κ | Adm κ} R

end main

end WaveTurbulence.GammaLow.FinalCount.H
