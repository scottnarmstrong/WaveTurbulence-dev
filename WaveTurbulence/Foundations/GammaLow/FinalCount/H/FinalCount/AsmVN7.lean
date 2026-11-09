/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmHmem
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN7`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 7): the state-level facts `VFacts` of a vine cut along an intact collected object.**
`VHard` is the part of `VFacts` that needs the garden's vine classification (`hcls`, `hconn`, `hrho`, `hint`: named inputs of the class,
see HANDOFF); everything else (`hu hl h3a h3b hdu hdl hnl`) is proved here from `UIntact`, `SubHyp` and the hinge data of the object. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The garden-dependent fields of `VFacts`. -/
structure VHard (crit : V → Prop) (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) : Prop where
  hcls : ∀ (R : ℝ) (kp : ℕ) (K' : Step1.VineCut Src.γL h.s.M) (R' : ℝ) (kp' : ℕ), h.vinePostL K R kp = h.vinePostL K' R' kp' →
    Step1.SingleVineVCGamma K' ∨ Nonempty (Step1.DoubleShape K')
  hconn : ∀ (R : ℝ) (kp : ℕ) (K' : Step1.VineCut Src.γL h.s.M) (R' : ℝ) (kp' : ℕ), h.vinePostL K R kp = h.vinePostL K' R' kp' →
    Nonempty (Step1.DoubleShape K') → ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G
  hrho : h.s.M.rho ≤ K.post.rho + 86
  hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a

/-- The oriented joint pair of `U` determines the hinge pair. -/
theorem pair_set_eq {M : Molecule V D₀} (U : Src.Object Src.γL M) {v : V} {p q f s : D₀} (hpq : SourceObjectJointPair U v p q)
    (hv : v = U.upper ∨ v = U.lower) (hf : U.ContainsDart f) (hs : U.ContainsDart s) (haf : M.atom f = v)
    (has : M.atom s = v) (hout : M.out f ≠ M.out s) : ({q, p} : Set D₀) = {f, s} := by
  have hf' := cd_at_joint_eq U hv hpq.1 hpq.2.1 hpq.2.2.1 hpq.2.2.2.1 hpq.2.2.2.2.1 hpq.2.2.2.2.2 haf hf
  have hs' := cd_at_joint_eq U hv hpq.1 hpq.2.1 hpq.2.2.1 hpq.2.2.2.1 hpq.2.2.2.2.1 hpq.2.2.2.2.2 has hs
  have hpq' : p ≠ q := fun e => by have := hpq.2.2.2.2.1; have := hpq.2.2.2.2.2; simp_all
  rcases hf' with rfl | rfl <;> rcases hs' with rfl | rfl
  · exact absurd rfl hout
  · exact Set.pair_comm _ _
  · rfl
  · exact absurd rfl hout

end WaveTurbulence.GammaLow.FinalCount.H
