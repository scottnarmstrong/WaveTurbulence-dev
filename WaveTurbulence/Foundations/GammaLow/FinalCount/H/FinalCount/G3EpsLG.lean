/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3EpsLG
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Init
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3EpsLG`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3**: "any `ε`-atom in `𝕄_fin` must be LG in the decoration" (DH23 Prop 9.5, L1809--L1810). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- **"Any `ε`-atom in `𝕄_fin` must be LG in the decoration"** (DH23 Prop 9.5, L1809). -/
theorem Run.eps_LG {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf) (hS : SubHyp R M₀)
    (hdeg : DegenSG M₀ L γ η w κ) :
    ∀ a ∈ sf.M.atoms, sf.cls a = .eps → ∀ x y : sf.D, sf.M.atom x = a → sf.M.atom y = a →
      sf.M.out x = false → sf.M.out y = true → y ≠ sf.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ sf.down) x y) = .LG := by
  intro a ha hae x y hx hy hox hoy hxy
  have hrel := hr.dartRel
  obtain ⟨s₁, s₂, s₃, _, _, _, _, _, hsg, h4, _⟩ := hr
  obtain ⟨ha3, hae3⟩ := step4_rtg_eps h4 ha hae
  have hnsg : ¬ SGat M₀ L γ η w κ a := hsg a ha3 hae3
  have hx0 : M₀.atom (sf.down x) = a := by rw [hrel.eps x (by rw [hx]; exact hae), hx]
  have hy0 : M₀.atom (sf.down y) = a := by rw [hrel.eps y (by rw [hy]; exact hae), hy]
  have hox0 : M₀.out (sf.down x) = false := by rw [hrel.out]; exact hox
  have hoy0 : M₀.out (sf.down y) = true := by rw [hrel.out]; exact hoy
  have hxy0 : sf.down y ≠ M₀.mate (sf.down x) := by
    intro e
    have := hS.noloop (sf.down x)
    rw [← e, hx0, hy0] at this
    exact this rfl
  have haM : a ∈ M₀.atoms := hx0 ▸ M₀.atom_mem _
  have hgap : Molecule.gapAt L w (κ ∘ sf.down) x y = Molecule.gapAt L w κ (sf.down x) (sf.down y) := rfl
  rw [hgap]
  by_contra hne
  have hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) = .SG ∨
      Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) = .ZG := by
    rcases hk : Molecule.gapKind L γ η (Molecule.gapAt L w κ (sf.down x) (sf.down y)) with _ | _ | _
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact absurd hk hne
  rcases hk with hk | hk
  · exact hnsg ⟨sf.down x, sf.down y, hx0, hy0, hox0, hoy0, hxy0, hk⟩
  · exact hnsg (hdeg a haM _ _ hx0 hy0 hox0 hoy0 hxy0 hk)


end WaveTurbulence.GammaLow.FinalCount.H
