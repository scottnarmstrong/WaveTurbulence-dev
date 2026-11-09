/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-1 (3): the LOW reach relations.**  `HStep1RL` = the restricted Step 1 of the REG chain (`HStep1R`, R49) plus the
Step D1 at a collected object with a degree-`2` joint; `Reach1L`; the D3 phase (`ReachD3`) between `Stuck1` and Step 2; `Reach2L/3L/4L`;
`Reach4L.toRunLC` (the run `HRunLC` of G3-LOWDEG). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section defs
variable {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d)

/-- **The restricted Step 1 of the LOW run** (R49): the REG steps `HStep1R`, and Step D1 at a collected object `U` with a joint of degree
`2` (same data as the `vine` constructor of `HStep1R`: `U.atoms = K.C.atoms`, darts, joints, first-stage order). -/
inductive HStep1RL (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | old {h h' : HSt V D₀} (hs : HStep1R C Un Fst L γ η w κ h h') : HStep1RL κ h h'
  | d1 (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (hs : HStepD1 C L γ η w κ h (h.vinePostGL K))
      (U : Src.Object Src.γL M₀) (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
      (hUD : U.ContainsDart (h.s.down K.x₁) ∧ U.ContainsDart (h.s.down K.x₂) ∧ U.ContainsDart (h.s.down K.y₁) ∧
        U.ContainsDart (h.s.down K.y₂))
      (hUJ : (M₀.atom (h.s.down K.x₁) = U.upper ∧ M₀.atom (h.s.down K.y₁) = U.lower) ∨
        (M₀.atom (h.s.down K.x₁) = U.lower ∧ M₀.atom (h.s.down K.y₁) = U.upper))
      (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h) : HStep1RL κ h (h.vinePostGL K)

theorem HStep1RL.toL {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀} (hs : HStep1RL C Un Fst L γ η w κ h h') :
    HStep1L C L γ η w κ h h' := by
  cases hs with
  | old hs => exact HStep1L.old hs.toC
  | d1 K hs _ _ _ _ _ _ => exact HStep1L.low hs

/-- The reach relation of Step 1 in the LOW run. -/
def Reach1L (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  Relation.ReflTransGen (HStep1RL C Un Fst L γ η w κ) (HSt.init M₀) h

/-- The D3 phase: from a Step-1-stuck state, degree-`2` cuts. -/
def ReachD3 (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁, Reach1L C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h

def Reach2L (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂, Reach1L C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧
    NoD3 C L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h

def Reach3L (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃, Reach1L C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧
    NoD3 C L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₃ h

def Reach4L (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃ h₄, Reach1L C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStepD3 C L γ η w κ) h₁ h₂ ∧
    NoD3 C L w κ h₂ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₂ h₃ ∧ NoEligibleTriangle C L γ η w κ h₃ ∧
    Relation.ReflTransGen (HStep3C C L γ η w κ) h₃ h₄ ∧ NoSGLeft L γ η w κ (HSt.init M₀).s h₄.s ∧
    Relation.ReflTransGen (HStep4 L w κ) h₄ h

variable {C Un Fst L γ η w}

theorem Reach1L.toL {κ} {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) :
    Relation.ReflTransGen (HStep1L C L γ η w κ) (HSt.init M₀) h :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.toL) _ _ hr

theorem Reach1L.ext {κ} {h h' : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) (hs : HStep1RL C Un Fst L γ η w κ h h') :
    Reach1L C Un Fst L γ η w κ h' := Relation.ReflTransGen.tail hr hs

theorem ReachD3.ext {κ} {h h' : HSt V D₀} (hr : ReachD3 C Un Fst L γ η w κ h) (hs : HStepD3 C L γ η w κ h h') :
    ReachD3 C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, a, b, c.tail hs⟩

theorem Reach2L.ext {κ} {h h' : HSt V D₀} (hr : Reach2L C Un Fst L γ η w κ h) (hs : HStep2C C L γ η w κ h h') :
    Reach2L C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, a, b, c, d', e.tail hs⟩

theorem Reach3L.ext {κ} {h h' : HSt V D₀} (hr : Reach3L C Un Fst L γ η w κ h) (hs : HStep3C C L γ η w κ h h') :
    Reach3L C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, h₂, h₃, a, b, c, d', e, f, g⟩ := hr; exact ⟨h₁, h₂, h₃, a, b, c, d', e, f, g.tail hs⟩

theorem Reach4L.ext {κ} {h h' : HSt V D₀} (hr : Reach4L C Un Fst L γ η w κ h) (hs : HStep4 L w κ h h') :
    Reach4L C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, h₂, h₃, h₄, a, b, c, d', e, f, g, i, j⟩ := hr; exact ⟨h₁, h₂, h₃, h₄, a, b, c, d', e, f, g, i, j.tail hs⟩

theorem Reach1L.toD3 {κ} {h : HSt V D₀} (hr : Reach1L C Un Fst L γ η w κ h) (hs : Stuck1 C L γ η w Un κ h) :
    ReachD3 C Un Fst L γ η w κ h := ⟨h, hr, hs, Relation.ReflTransGen.refl⟩

theorem ReachD3.to2 {κ} {h : HSt V D₀} (hr : ReachD3 C Un Fst L γ η w κ h) (hs : NoD3 C L w κ h) :
    Reach2L C Un Fst L γ η w κ h := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, h, a, b, c, hs, Relation.ReflTransGen.refl⟩

theorem Reach2L.to3 {κ} {h : HSt V D₀} (hr : Reach2L C Un Fst L γ η w κ h) (hs : NoEligibleTriangle C L γ η w κ h) :
    Reach3L C Un Fst L γ η w κ h := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, h, a, b, c, d', e, hs, Relation.ReflTransGen.refl⟩

theorem Reach3L.to4 {κ} {h : HSt V D₀} (hr : Reach3L C Un Fst L γ η w κ h) (hs : NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    Reach4L C Un Fst L γ η w κ h := by
  obtain ⟨h₁, h₂, h₃, a, b, c, d', e, f, g⟩ := hr; exact ⟨h₁, h₂, h₃, h, a, b, c, d', e, f, g, hs, Relation.ReflTransGen.refl⟩

/-- **The run `HRunLC` of G3-LOWDEG from `Reach4L` at a state where Step 4 stops.** -/
theorem Reach4L.toRunLC {κ} {h : HSt V D₀} (hr : Reach4L C Un Fst L γ η w κ h) (hn : NoBetaCut L w κ h.s) :
    HRunLC L γ η w κ M₀ h C (Un κ) := by
  obtain ⟨h₁, h₂, h₃, h₄, a, ⟨b1, b2⟩, c, d', e, f, g, i, j⟩ := hr
  exact ⟨h₁, h₂, h₃, h₄, a.toL, b1, c, d', e, f, g, i, j, hn, fun U hU x => b2 U (by
    rcases hU with hU | hU
    · exact Or.inl hU
    · exact Or.inr hU) x⟩

end defs

end WaveTurbulence.GammaLow.FinalCount.H
