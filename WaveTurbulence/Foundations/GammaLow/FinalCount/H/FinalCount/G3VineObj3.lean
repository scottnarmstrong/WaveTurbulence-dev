/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineObj3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Bal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Final2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Prop95
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RelRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.Prop95Core
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3VineObj2
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineObj3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: identification of a final vine component, part 5** (E10): the packaged `Object M_sub`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- **E10**: a final component that is a vine with non-`ε` joints of degree `2` and `ε` interior atoms of degree
`4` is, after replacing the joints by their ancestors, a vine-like object `P` of `M_sub`
(a VC, or an HV when the other halves of the joints are joined by a bond), and the gap of `P` is the gap at the joint. -/
theorem final_vine_object {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHyp R M₀) (hv : Src.IsSomeVine Src.γL (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms j₁ j₂) :
    ∃ P : Src.Object Src.γL M₀, P.atoms = AncGroup hf a₀ ∧ P.upper = hf.anc j₁ ∧ P.lower = hf.anc j₂ ∧
      ∀ (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (y y' : hf.s.D), hf.s.M.atom y = j₁ → hf.s.M.atom y' = j₁ →
        hf.s.M.out y = false → hf.s.M.out y' = true →
        ∃ r, P.shape.IsGap L w κ r ∧ r = Molecule.gapAt L w (κ ∘ hf.s.down) y' y := by
  have hy : ∀ y : hf.s.D, hf.s.M.atom y = j₁ → hf.s.M.SameComponent a₀ (hf.s.M.atom y) := fun y h => by
    rw [h]; exact J.c1
  rcases extras_cases J hA hD hS with hne | ⟨e, he, hall⟩
  · have hvM := TV.final_vine_vcS J hA hD hS hv hne
    have G := comp_groupIso hA hD a₀ (J.injOn hA hD hS) (fun z hz => by
      by_contra hc
      exact hne z ⟨hz, hc⟩)
    refine ⟨⟨AncGroup hf a₀, hf.anc j₁, hf.anc j₂, .vc ⟨hvM.block, 1, Src.Chain.single hvM⟩⟩, rfl, rfl, rfl, ?_⟩
    intro L w κ y y' hy1 hy1' hyo hyo'
    refine ⟨_, ?_, rfl⟩
    refine ⟨compEmb hf a₀ ⟨y', hy y' hy1'⟩, compEmb hf a₀ ⟨y, hy y hy1⟩, ?_, ?_, G.inGroup _, G.inGroup _, ?_, ?_, rfl⟩
    · show M₀.atom (hf.s.down y') = hf.anc j₁
      rw [hA.atom, hy1']
    · show M₀.atom (hf.s.down y) = hf.anc j₁
      rw [hA.atom, hy1]
    · show M₀.out (hf.s.down y') = true
      rw [hD.out]; exact hyo'
    · show M₀.out (hf.s.down y) = false
      rw [hD.out]; exact hyo
  · obtain ⟨hends, hvM⟩ := TV.final_vine_hvS J hA hD hS hv he hall
    obtain ⟨ι, hι, G⟩ := hv_groupIso J hA hD hS he hall
    refine ⟨⟨AncGroup hf a₀, hf.anc j₁, hf.anc j₂, .hyper ⟨e, hends, ⟨hvM.block, 1, Src.Chain.single hvM⟩⟩⟩,
      rfl, rfl, rfl, ?_⟩
    intro L w κ y y' hy1 hy1' hyo hyo'
    refine ⟨_, ?_, rfl⟩
    refine ⟨ι ⟨y', hy y' hy1'⟩, ι ⟨y, hy y hy1⟩, ?_, ?_, G.inGroup _, G.inGroup _, ?_, ?_, ?_⟩
    · show M₀.atom (ι ⟨y', hy y' hy1'⟩).1 = hf.anc j₁
      rw [hι]; show M₀.atom (hf.s.down y') = hf.anc j₁
      rw [hA.atom, hy1']
    · show M₀.atom (ι ⟨y, hy y hy1⟩).1 = hf.anc j₁
      rw [hι]; show M₀.atom (hf.s.down y) = hf.anc j₁
      rw [hA.atom, hy1]
    · show M₀.out (ι ⟨y', hy y' hy1'⟩).1 = true
      rw [hι]; show M₀.out (hf.s.down y') = true
      rw [hD.out]; exact hyo'
    · show M₀.out (ι ⟨y, hy y hy1⟩).1 = false
      rw [hι]; show M₀.out (hf.s.down y) = false
      rw [hD.out]; exact hyo
    · show Molecule.gapAt L w (κ ∘ hf.s.down) y' y = Molecule.gapAt L w (fun x => κ x.1) (ι ⟨y', hy y' hy1'⟩) (ι ⟨y, hy y hy1⟩)
      simp only [Molecule.gapAt, Molecule.kvec, Function.comp]
      rw [hι, hι]; rfl

end WaveTurbulence.GammaLow.FinalCount.H
