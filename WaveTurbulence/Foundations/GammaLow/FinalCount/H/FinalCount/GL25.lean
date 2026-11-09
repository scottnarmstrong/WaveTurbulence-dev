/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL25
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL23
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GM08
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL25`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 25: `Object.noLoop_of_SG`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

/-- **An object of `M.unloop` with a small (SG) gap contains no loop atom of `M`.**  Hypotheses: the `ε`-support (`heq`: all legs of a
loop atom carry the same label), the conservation hypotheses `hκ`, `h0` of the decoration, and the standing hypothesis `SubHypL` of
`M.unloop`. -/
theorem Src.Object.noLoop_of_SG {R' : ℕ} {M : Molecule V D} (hS : SubHypL R' M.unloop) (hb : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (L γ η : ℝ) (w : Mom d) (κ : D → Fin d → ℤ) (hκ : ∀ x, κ (M.mate x) = κ x)
    (heq : ∀ y : D, M.atom y = M.atom (M.mate y) → ∀ z : D, M.atom z = M.atom y → κ z = κ y)
    (h0 : ∀ a ∈ M.unloop.atoms, M.unloop.deg a = 4 →
      ∑ x ∈ M.unloop.dartsAt a, M.unloop.dartSign x • Molecule.kvec L w (fun y : NonLoop M => κ y.1) x = 0)
    (P : Src.Object Src.γL M.unloop) (hSG : P.HasGapKind L γ η w (fun y : NonLoop M => κ y.1) .SG) : LoopFreeSet M P.atoms := by
  have hM := hS.isMolecule
  intro y hy hloop
  obtain ⟨S, a, b, sh⟩ := P
  have hy : M.atom y ∈ S := hy
  have hv4 : M.deg (M.atom y) ≤ 4 := hb _ (M.atom_mem y)
  have hdeg2 : M.unloop.deg (M.atom y) ≤ 2 := loop_deg_le M rfl hloop.symm hv4
  have hl : ∃ y', M.atom y' = M.atom y ∧ M.atom (M.mate y') = M.atom y := ⟨y, rfl, hloop.symm⟩
  have hκ' : ∀ x : NonLoop M, (fun y : NonLoop M => κ y.1) (M.unloop.mate x) = (fun y : NonLoop M => κ y.1) x :=
    fun x => hκ x.1
  cases sh with
  | vc hv' =>
    have hB : M.unloop.IsBlock S a b := hv'.1
    by_cases hj : M.atom y = a ∨ M.atom y = b
    · obtain ⟨r, hr, hk⟩ := hSG
      have hr' : M.unloop.IsBlockGap L w (fun y : NonLoop M => κ y.1) S a r := hr
      rcases hj with hj | hj
      · obtain ⟨x₁, x₂, h1, h2, -, -, -, -, hrr⟩ := hr'
        have h1' : M.atom x₁.1 = M.atom y := h1.trans hj.symm
        have h2' : M.atom x₂.1 = M.atom y := h2.trans hj.symm
        have := gap_zero_at_loop M L w heq hl x₁ x₂ h1' h2'
        rw [hrr, this, gapKind_zero] at hk
        exact absurd hk (by decide)
      · obtain ⟨r', hr'', hk'⟩ := source_block_lower_SG_gap M.unloop hM hB L γ η w _ hκ' h0 hr' hk
        obtain ⟨x₁, x₂, h1, h2, -, -, -, -, hrr⟩ := hr''
        have h1' : M.atom x₁.1 = M.atom y := h1.trans hj.symm
        have h2' : M.atom x₂.1 = M.atom y := h2.trans hj.symm
        have := gap_zero_at_loop M L w heq hl x₁ x₂ h1' h2'
        rw [hrr, this, gapKind_zero] at hk'
        exact absurd hk' (by decide)
    · push Not at hj
      have hd := hB.2.2.2.2.2.2.2.2.1 (M.atom y) hy hj.1 hj.2
      have := degIn_le_deg' M.unloop S (M.atom y)
      omega
  | hyper R =>
    have hB : (M.unloop.eraseBond R.added).IsBlock S a b := R.adjoint.1
    have hN := erase_deg_le M.unloop R.added (M.atom y)
    by_cases hj : M.atom y = a ∨ M.atom y = b
    · -- a joint of the adjoint: two darts in the group plus the added bond
      have hout : (M.unloop.eraseBond R.added).outIn S (M.atom y) = 1 ∧ (M.unloop.eraseBond R.added).inIn S (M.atom y) = 1 := by
        rcases hj with hj | hj <;> rw [hj]
        · exact ⟨hB.2.2.2.2.1, hB.2.2.2.2.2.1⟩
        · exact ⟨hB.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.1⟩
      have h1 := outIn_le_outdeg (M.unloop.eraseBond R.added) S (M.atom y)
      have h2 := inIn_le_indeg (M.unloop.eraseBond R.added) S (M.atom y)
      have h3 := deg_eq (M := M.unloop.eraseBond R.added) (M.atom y)
      have hd0 : ∃ d₀, M.unloop.atom d₀ = M.atom y ∧ (d₀ = R.added ∨ d₀ = M.unloop.mate R.added) := by
        have he := R.ends_eq
        unfold Molecule.ends at he
        rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rcases hj with hj | hj
          · exact ⟨R.added, by rw [hj]; exact e1, Or.inl rfl⟩
          · exact ⟨M.unloop.mate R.added, by rw [hj]; exact e2, Or.inr rfl⟩
        · rcases hj with hj | hj
          · exact ⟨M.unloop.mate R.added, by rw [hj]; exact e2, Or.inr rfl⟩
          · exact ⟨R.added, by rw [hj]; exact e1, Or.inl rfl⟩
      have := erase_deg_lt M.unloop R.added (M.atom y) hd0
      omega
    · push Not at hj
      have hd := hB.2.2.2.2.2.2.2.2.1 (M.atom y) hy hj.1 hj.2
      have := degIn_le_deg' (M.unloop.eraseBond R.added) S (M.atom y)
      omega

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Object.noLoop_of_SG := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Object.noLoop_of_SG
end WaveTurbulence.GammaLow.FinalCount.H
