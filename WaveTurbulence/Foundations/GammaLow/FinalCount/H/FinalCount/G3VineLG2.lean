/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineObj4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3VineLG2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `vineLG`, part 2: darts of a final vine component seen in `M_sub`.** -/
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

theorem contains_of (U : Src.Object Src.γL M₀) (z : D₀) (hg : M₀.InGroup U.atoms z)
    (hn : ∀ R, U.shape = Src.VineLikeObject.hyper R → z ≠ R.added ∧ z ≠ M₀.mate R.added) : U.ContainsDart z := by
  unfold Src.Object.ContainsDart
  rcases hsh : U.shape with hvc | R'
  · exact hg
  · exact ⟨(hn R' hsh).1, (hn R' hsh).2, hg⟩

/-- **Use 1 (Step 1 removes the collection).**  An object of `M_sub` whose atom set contains the ancestor group of a final vine
component contains a dart that is the image of a final dart. -/
theorem final_dart_contained (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hnl : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) (U : Src.Object Src.γL M₀)
    (hU : AncGroup hf a₀ ⊆ U.atoms) : ∃ x : hf.s.D, U.ContainsDart (hf.s.down x) := by
  obtain ⟨x, y, hx, hy, hxy, hym, -⟩ := joint_two_darts hnl J.d1
  have gx : M₀.InGroup U.atoms (hf.s.down x) := by
    have := inGroup_down hA hD x (by rw [hx]; exact J.c1)
    exact ⟨hU this.1, hU this.2⟩
  have gy : M₀.InGroup U.atoms (hf.s.down y) := by
    have := inGroup_down hA hD y (by rw [hy]; exact J.c1)
    exact ⟨hU this.1, hU this.2⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ z : hf.s.D, M₀.InGroup U.atoms (hf.s.down z) → ¬ U.ContainsDart (hf.s.down z) →
      ∃ R, U.shape = Src.VineLikeObject.hyper R ∧ (hf.s.down z = R.added ∨ hf.s.down z = M₀.mate R.added) := by
    intro z gz hn
    by_contra h'
    push Not at h'
    exact hn (contains_of U _ gz fun R hR => h' R hR)
  obtain ⟨R1, h1, e1⟩ := key x gx (hcon x)
  obtain ⟨R2, h2, e2⟩ := key y gy (hcon y)
  have hR : R1 = R2 := by
    have := h1.symm.trans h2
    exact Src.VineLikeObject.hyper.inj this
  subst hR
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact hxy (hA.inj (e1.trans e2.symm))
  · exact hym (hA.inj (by rw [e2, ← hD.mate, e1]))
  · exact hym (hA.inj (by rw [← hD.mate, e1, M₀.mate_mate, e2]))
  · exact hxy (hA.inj (e1.trans e2.symm))

end WaveTurbulence.GammaLow.FinalCount.H
