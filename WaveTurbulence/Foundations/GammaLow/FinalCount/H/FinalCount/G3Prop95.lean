/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Prop95
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Bal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CycChain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Final2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3N12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Prop95`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: assembly of DH23 Proposition 9.5 (`finalmole`, L1806) / TARGET `finalmol` (L2182)** from the
proved parts: `HRun.core`, `HRun.cycles`, `HRun.chains` and the dart-level data. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

theorem HRun.prop95 [Infinite V] {M₀ : Molecule V D₀} {hf : HSt V D₀}
    (hr : HRun L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀) (hdeg : DegenSG M₀ L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95Concl L γ η w κ R hf := by
  have hc := hr.core hS hdeg h0
  have hI := hr.runInv hS h0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, n4⟩ := id hr
  exact
  { struct := hc.struct
    label := hc.label
    eps_LG := hc.eps_LG
    no_triple := hc.no_triple
    cycles := hr.cycles hS h0
    chains := hr.chains hS hdeg
    N1 := hc.N1
    N2 := hc.N2
    bal := hr.toRun.bal hS
    noloop := hI.good.1.noloop
    alpha_sg := hr.alpha_sg hS h0
    dartGap := by
      intro a ha hne x y hx hy hox hoy
      obtain ⟨p, vis, hrec, hn⟩ := hI.gap.dg a ha hne x y hx hy hox hoy
      exact ⟨pgap L w κ p, ⟨p, vis, hrec, rfl⟩, hn⟩
    noBetaCut := n4 }

end WaveTurbulence.GammaLow.FinalCount.H
