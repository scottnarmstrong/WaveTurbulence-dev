/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV04
public import WaveTurbulence.Foundations.FinalCount.G3VineObj3
/-! **G3-LOWDEG port of `G3VineObj3`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

/-- **E10**: a final component that is a vine with non-`ε` joints of degree `2` and `ε` interior atoms of degree
`4` is, after replacing the joints by their ancestors, a vine-like object `P` of `M_sub`
(a VC, or an HV when the other halves of the joints are joined by a bond), and the gap of `P` is the gap at the joint. -/
theorem final_vine_objectL {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hS : SubHypL R M₀) {X : VineType}
    (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂) :
    ∃ P : Object M₀, P.atoms = AncGroup hf a₀ ∧ P.upper = hf.anc j₁ ∧ P.lower = hf.anc j₂ ∧
      ∀ (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (y y' : hf.s.D), hf.s.M.atom y = j₁ → hf.s.M.atom y' = j₁ →
        hf.s.M.out y = false → hf.s.M.out y' = true →
        ∃ r, P.shape.IsGap L w κ r ∧ r = Molecule.gapAt L w (κ ∘ hf.s.down) y' y := by
  have hy : ∀ y : hf.s.D, hf.s.M.atom y = j₁ → hf.s.M.SameComponent a₀ (hf.s.M.atom y) := fun y h => by
    rw [h]; exact J.c1
  rcases extras_casesL J hA hD hS with hne | ⟨e, he, hall⟩
  · have hvM := final_vine_vcL J hA hD hS hv hne
    have G := comp_groupIso hA hD a₀ (J.injOnL hA hD hS) (fun z hz => by
      by_contra hc
      exact hne z ⟨hz, hc⟩)
    refine ⟨⟨AncGroup hf a₀, hf.anc j₁, hf.anc j₂, .vc ⟨hvM.1, 1, Chain.single ⟨X, hvM⟩⟩⟩, rfl, rfl, rfl, ?_⟩
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
  · obtain ⟨hends, hvM⟩ := final_vine_hvL J hA hD hS hv he hall
    obtain ⟨ι, hι, G⟩ := hv_groupIsoL J hA hD hS he hall
    refine ⟨⟨AncGroup hf a₀, hf.anc j₁, hf.anc j₂, .hyper ⟨e, hends, ⟨hvM.1, 1, Chain.single ⟨X, hvM⟩⟩⟩⟩,
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

end WaveTurbulence.FinalCountG3

