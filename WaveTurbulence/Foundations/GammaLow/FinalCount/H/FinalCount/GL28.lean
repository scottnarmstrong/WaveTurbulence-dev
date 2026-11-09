/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL28
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL27
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GV14
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL28`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 28: the loop start, assembled.**  `runDataL_of_loop`: a garden molecule `M` with self-loops, with the
producers' data on `M` (the same data as in the loop-free case: `C`, `Unsel`, `SubproOblG`, `TripleDesig`, `UnselOK`) and the
run on `M.unloop`, gives `RunDataL` for `M.unloop` with the admissible set `unloopAdm`.  Together with `countA_unloop_le` (GL17),
`SubHypLoop.unloop` (GL18): `𝔄(M) ≤ g^k 𝔄(M.unloop)`, `M.unloop` satisfies `SubHypL (R+k)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
universe u
variable {V : Type*} [DecidableEq V] {D : Type u} [Fintype D] [DecidableEq D] {d : ℕ}
variable {R' : ℕ} {M : Molecule V D} {L γ η : ℝ}

theorem runDataL_of_loop {hf : HSt V (NonLoop M)} (Adm : (D → Fin d → ℤ) → Prop)
    (hctx : ∀ κ, Adm κ → LoopCtx L (0 : Mom d) κ R' M)
    (hdata : ∀ κ, Adm κ → ∃ (C : CollData M) (Unsel : Set (Src.Object Src.γL M)), SubproOblG C L γ η (0 : Mom d) κ ∧ TripleDesig C ∧
      HingeNoLoop C ∧ C.UnselOK L γ η (0 : Mom d) κ Unsel ∧
      HRunLC L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) M.unloop hf C.unloop (unloopSet M Unsel)) :
    RunDataL L γ η M.unloop hf (unloopAdm M Adm) := by
  rintro κ' ⟨κ, hκ, rfl⟩
  obtain ⟨C, Unsel, obl, hT3, hH, hU, hrun⟩ := hdata κ hκ
  exact ⟨C.unloop, unloopSet M Unsel, SubproOblG.unloopL (hctx κ hκ) hH obl, TripleDesig.unloopL hH hT3,
    UnselOK.unloopL (hctx κ hκ) hH obl hU, hrun⟩

/-- The whole loop-start package at the level of the molecule: `M.unloop` satisfies `SubHypL (R + k)`, and its `h0`, `DegenSGT`. -/
theorem loopStart {R : ℕ} (hS : SubHypLoop R M) {κ : D → Fin d → ℤ} (hκ : ∀ x, κ (M.mate x) = κ x) {Tm : V → Prop}
    (hdeg : DegenSGT M L γ η (0 : Mom d) κ Tm)
    (h0 : ∀ a ∈ M.atoms, M.deg a = 4 → ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0)
    (heq : ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y) :
    SubHypL (R + M.loopBonds.card) M.unloop ∧ LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M ∧
      DegenSGT M.unloop L γ η (0 : Mom d) (fun y : NonLoop M => κ y.1) Tm ∧
      (∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 → ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x •
        Molecule.kvec L (0 : Mom d) (fun y : NonLoop M => κ y.1) x = 0) := by
  have hb : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hS.bounds a ha)
  have h0' := h0_unloop hS hκ h0
  have hctx : LoopCtx L (0 : Mom d) κ (R + M.loopBonds.card) M := ⟨hS.unloop, hb, hκ, heq, h0'⟩
  exact ⟨hS.unloop, hctx, DegenSGT.unloopL hctx hdeg, h0'⟩

end WaveTurbulence.GammaLow.FinalCount.H
