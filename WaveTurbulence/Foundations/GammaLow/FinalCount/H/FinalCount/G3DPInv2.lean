/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3DPInv2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3DPInv2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `DPInv` is preserved by Steps 1--4.** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

private theorem inj_cutSt {s : St.{u} V D₀} (hinj : Function.Injective s.down) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) :
    Function.Injective (s.cutSt v v₂ x₁ x₂ c₁ c₂).down := hinj

theorem HStep1.dp {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hI : DPInv h)
    (hinj : Function.Injective h.s.down) : DPInv h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have e1 : ∀ p vis, (some (h.s.pr K.x₁ K.x₂, h.alive) : Option ((D₀ × D₀) × List (D₀ × D₀))) = some (p, vis) →
        p = h.s.pr K.x₁ K.x₂ := fun p vis e => by
      simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1.symm
    have e2 : ∀ p vis, (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive) : Option ((D₀ × D₀) × List (D₀ × D₀))) =
        some (p, vis) → p = h.s.pr K.y₁ K.y₂ := fun p vis e => by
      simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1.symm
    have g1 := hI.cut_gen hinj K.cut_a (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
      (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp) (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
      (na := Function.update h.anc K.fa (h.anc K.C.upper)) _ _ e1 e1
    have g2 := g1.cut_gen (inj_cutSt hinj _ _ _ _ _ _) K.cut_b (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
      (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp) (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
      (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) _ _ e2 e2
    exact g2.delSt _ K.closed

end WaveTurbulence.GammaLow.FinalCount.H
