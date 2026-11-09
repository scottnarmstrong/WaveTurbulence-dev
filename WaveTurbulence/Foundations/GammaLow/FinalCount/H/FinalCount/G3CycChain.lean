/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3CycChain
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
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3CycChain`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: `cycles` and `chains` for a run with history** (DH23 Prop 9.5, L1807). -/
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

/-- `NoSGTriangle` at the end of a run. -/
theorem Run.noSGTri {M₀ : Molecule V D₀} {sf : St.{u} V D₀} (hr : Run L γ η w κ (St.init M₀) sf)
    (hS : SubHyp R M₀) : NoSGTriangle L γ η w κ sf := by
  obtain ⟨s₁, s₂, s₃, h1, -, h2, n2, h3, -, h4, -⟩ := hr
  have g0 : Good R (St.init M₀) := ⟨hS.inv, St.init_clean M₀⟩
  have g2 := good_rtg (fun _ _ h g => Step2.good h g) h2 (good_rtg (fun _ _ h g => Step1.good h g) h1 g0)
  have k3 : ∀ {a b : St.{u} V D₀}, Relation.ReflTransGen (Step3 L γ η w κ) a b → Good R a →
      NoSGTriangle L γ η w κ a → Good R b ∧ NoSGTriangle L γ η w κ b := by
    intro a b hab
    induction hab with
    | refl => exact fun g n => ⟨g, n⟩
    | tail _ hs ih =>
      intro g n
      obtain ⟨g', n'⟩ := ih g n
      exact ⟨hs.good g', hs.noSGTri n' g'.1.noloop⟩
  have k4 : ∀ {a b : St.{u} V D₀}, Relation.ReflTransGen Step4 a b → Good R a →
      NoSGTriangle L γ η w κ a → NoSGTriangle L γ η w κ b := by
    intro a b hab
    induction hab with
    | refl => exact fun g n => n
    | tail _ hs ih =>
      intro g n
      have := ih g n
      exact hs.noSGTri this (by
        have gg : Good R _ := good_rtg (fun _ _ h g => Step4.good h g) ‹_› g
        exact gg.1.noloop)
  obtain ⟨g3, n3⟩ := k3 h3 g2 n2
  exact k4 h4 g3 n3

/-- Dart-level SG gaps of `α`-atoms (the recorded cut is SG and the dart gaps have its norm). -/
theorem HRun.alpha_sg {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ b ∈ hf.s.M.atoms, ∀ ρ kp, hf.s.cls b = .alpha ρ kp → ∀ x y : hf.s.D, hf.s.M.atom x = b →
      hf.s.M.atom y = b → hf.s.M.out x = false → hf.s.M.out y = true →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ hf.s.down) x y) = .SG := by
  intro b hb ρ kp hc x y hx hy hox hoy
  have hI := (hr.runInv hS h0).hrec
  have hG := (hr.runInv hS h0).gap
  obtain ⟨-, p, vis, hrec, -, -, -, hsg⟩ := (hI.ok b hb).1 ρ kp hc
  obtain ⟨p', vis', hrec', hn⟩ := hG.dg b hb (by rw [hc]; simp) x y hx hy hox hoy
  rw [hrec] at hrec'
  simp only [Option.some.injEq, Prod.mk.injEq] at hrec'
  obtain ⟨rfl, rfl⟩ := hrec'
  rw [gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_gap_of_pm hn)]
  exact hsg

theorem HRun.cycles [Infinite V] {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀)
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → (∀ b ∈ compAtoms hf.s.M a, hf.s.cls b ≠ .eps) → CycleShape hf.s a :=
  fun _ ha hev hne => cycles_of (hr.toRun.finalStruct hS).ab_deg (fun c hc => (hr.toRun.finalStruct hS).deg_range c hc |>.1)
    (BalS.ofM (hr.toRun.bal hS))
    (hr.runInv hS h0).good.1.noloop (hr.toRun.noSGTri hS) (hr.alpha_sg hS h0) ha hev hne

theorem HRun.chains [Infinite V] {M₀ : Molecule V D₀} {hf : HSt V D₀} (hr : HRun L γ η w κ (HSt.init M₀) hf)
    (hS : SubHyp R M₀) (hdeg : DegenSG M₀ L γ η w κ) :
    ∀ a ∈ hf.s.M.atoms, EvenComp hf.s.M a → hf.s.cls a ≠ .eps → (∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps) →
      ChainEnds hf.s a := by
  have hLG := hr.toRun.eps_LG hS hdeg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, n4⟩ := hr.toRun
  intro a ha hev hne hex
  exact chainEnds_of (hr.toRun.finalStruct hS).ab_deg (fun c hc => (hr.toRun.finalStruct hS).deg_range c hc |>.1)
    (BalS.ofM (hr.toRun.bal hS)) ha (fun e he hce _ v₂ x₁ x₂ hcd =>
      n4 e he ((hr.toRun.finalStruct hS).eps_deg e he hce) v₂ x₁ x₂ hcd
        (gapAt_ne_zero_of_LG (hLG e he hce x₁ x₂ hcd.2.2.1 hcd.2.2.2.1 hcd.2.2.2.2.2.1 hcd.2.2.2.2.2.2 hcd.2.2.2.2.1)))
    hev hne hex

end WaveTurbulence.GammaLow.FinalCount.H
