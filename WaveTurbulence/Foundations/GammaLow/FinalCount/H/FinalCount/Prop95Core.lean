/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop95Core
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Bal
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.Prop95Core`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: the proved fields of `Prop95Concl`** (`struct`, `label`, `eps_LG`, `N1`, `N2`). -/
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

theorem HRun.core {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf) (hS : SubHyp R M₀)
    (hdeg : DegenSG M₀ L γ η w κ)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    Prop95Core L γ η w κ R hf where
  struct := hr.toRun.finalStruct hS
  label := by
    intro a ha ρ kp hc
    have hI := (hr.runInv hS h0).hrec
    have hG := (hr.runInv hS h0).gap
    obtain ⟨hl, p, vis, hrec, hp, hkp, -, -⟩ := (hI.ok a ha).1 ρ kp hc
    refine ⟨hl, hkp, fun x y hx hy hox hoy _ => ?_⟩
    obtain ⟨p', vis', hrec', hn⟩ := hG.dg a ha (by rw [hc]; simp) x y hx hy hox hoy
    rw [hrec] at hrec'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
    obtain ⟨rfl, rfl⟩ := hrec'
    unfold GapSim
    rw [norm_gap_of_pm hn]
    exact hp
  eps_LG := hr.toRun.eps_LG hS hdeg
  no_triple := hr.toRun.noTriple (hr.runInv hS h0).good
  N1 := fun b hb hcb => (hr.runInv hS h0).hrec.N1 hb hcb
  N2 := fun hL hη v₁ h1 v₂ h2 b hb R₁ R₂ c1 c2 cb g₁ g₂ gb a1 a2 ab s₁ s₂ hs₁ hs₂ hsum =>
    (hr.runInv hS h0).hrec.N2 hL hη h1 h2 hb c1 c2 cb a1 a2 ab s₁ s₂ hs₁ hs₂ hsum

end WaveTurbulence.GammaLow.FinalCount.H
