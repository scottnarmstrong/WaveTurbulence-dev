/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Elig
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Elig`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3 (R29 item 1): eligible triangles.**  A triangle is ELIGIBLE iff its triples at `v₁, v₂` are SG, its pair at
`v₃` has nonzero gap, and at every hinge atom among `v₁, v₂, v₃` the triangle pair is one of the hinge's designated pairs
(the pair `{first, second}` or its complement; A1 of the referee).  `HStep2C` is `HStep2` restricted to eligible triangles. -/
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
/-- The pair `p` of darts of `M_sub` at the atom `a` is designated: if `a` is a hinge, `p` is the designated pair `{first, second}` or its
complement among the darts of `a` in `M_sub` (cutting a degree-`4` atom along a pair or along its complement is the same cut). -/
def Desig (C : CollData M₀) (a : V) (p : D₀ × D₀) : Prop :=
  a ∈ C.hinges → ∃ f s, C.first a = some f ∧ C.second a = some s ∧
    (({p.1, p.2} : Set D₀) = {f, s} ∨ ({p.1, p.2} : Set D₀) = (↑(M₀.dartsAt a) : Set D₀) \ {f, s})
/-- **Eligible triangle** (R29 item 1, A1). -/
def Eligible (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀)
    (T : TriData h.s.M) : Prop :=
  (∀ j : Fin 2, Molecule.gapKind L γ η
      (Molecule.gapAt L w (κ ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG) ∧
    pgap L w κ (h.s.pr (T.a 2) (T.b 2)) ≠ 0 ∧
    ∀ j : Fin 3, Desig C (h.anc (T.t j)) (h.s.pr (T.a j) (T.b j))
/-- Step 2 stops: no eligible triangle remains. -/
def NoEligibleTriangle (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∀ T : TriData h.s.M, ¬ Eligible C L γ η w κ h T
/-- **Step 2 on an eligible triangle only.** -/
inductive HStep2C (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | mk {h h' : HSt V D₀} (T : TriData h.s.M) (hel : Eligible C L γ η w κ h T)
      (hs : HStep2 L γ η w κ h h') (hT : ∃ Q kp hcl, h' = (⟨triSt h.s T Q kp hcl,
         h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist,
         Function.update (Function.update (Function.update h.crec (T.f 0) (some (h.s.pr (T.a 0) (T.b 0), h.alive)))
           (T.f 1) (some (h.s.pr (T.a 1) (T.b 1), h.triVis1 T)))
           (T.f 2) (some (h.s.pr (T.a 2) (T.b 2), h.triVis2 T)),
         Function.update (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1)))
           (T.f 2) (h.anc (T.t 2))⟩ : HSt V D₀)) :
      HStep2C C L γ η w κ h h'
theorem HStep2C.toHStep2 {C : CollData M₀} {h h' : HSt V D₀} (hs : HStep2C C L γ η w κ h h') :
    HStep2 L γ η w κ h h' := by
  cases hs with
  | mk _ _ hs _ => exact hs
end WaveTurbulence.GammaLow.FinalCount.H
