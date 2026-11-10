/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex34
public import WaveTurbulence.Foundations.FinalCount.G3Ex2
public import WaveTurbulence.Foundations.FinalCount.G3RunN
/-! **FINALCOUNT-ASSEMBLY: the named inputs, each stated once so that it can be swapped for a theorem at one place.**

All former named inputs (`NoTripleAfterStep1`, `AliveHit`, `GhostTriangleStep`) are gone: G3 #14 proves them (R37 triple cut, alive-cut `ι`)
or states them as `GhostTriInput` (the only remaining triangle named input).  This module keeps the potential ingredients. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {M₀ : Molecule V D₀}

/-- Number of `β` atoms and the `α`-product of a state (the potential's ingredients). -/
noncomputable def vBeta (s : St.{u} V D₀) : ℕ := (s.M.atoms.filter (fun a => s.cls a = .beta)).card

noncomputable def apFactor (L γ η : ℝ) : Cls → ℝ
  | .alpha R kp => L ^ ((γ + 3 * η) / 2 - (kp : ℝ) * η) * R
  | _ => 1

noncomputable def apProd (L γ η : ℝ) (s : St.{u} V D₀) : ℝ := ∏ a ∈ s.M.atoms, apFactor L γ η (s.cls a)

/-- The right side of a step in potential form: `L^{-η³} · L^{aΔF - bΔVβ} · ∏(new α factors)` where the differences are those of
the states (`a = 2γ₀+5η²`, `b = γ₀+2η²`, `γ₀ = min γ (1-γ)`). -/
noncomputable def stepRHS (L γ η : ℝ) (h h' : HSt V D₀) : ℝ :=
  L ^ (-η ^ 3) * L ^ ((2 * min γ (1 - γ) + 5 * η ^ 2) * ((h'.s.M.numComponents : ℝ) - h.s.M.numComponents)
      - (min γ (1 - γ) + 2 * η ^ 2) * ((vBeta h'.s : ℝ) - vBeta h.s)) * (apProd L γ η h'.s / apProd L γ η h.s)

end WaveTurbulence.FinalCountAsm
