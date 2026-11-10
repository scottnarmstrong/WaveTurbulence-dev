/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3FinalCopy`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3: local copy of G8's `Cls`, `FinalShape`, `FinalDec`** (from
`/home/scott/wt-scratch/finalcount-g8/Prop96Statement.lean`, sha256 in COPIED-SHA256SUMS; copied at first read
2026-11-05 00:3x UTC) so that the mapping theorem does not depend on G8's heavy imports.  Differences from the original:
the namespace (`G8Copy`), the local `crossDarts` (identical body to `MoleProp4.crossDarts`), and the single field
`oddDeg`, which is weakened (see the docstring there and HANDOFF F-ODD). -/
@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3.G8Copy
open WaveTurbulence

namespace Cls
open WaveTurbulence.FinalCountG3.G8Copy.Cls
end Cls

open Classical in
open Classical in
open Classical in
open Classical in
/-- **Prop 9.5 (L1806) and the history properties of R18, conclusions about the decoration.** -/
structure FinalDec {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) {d : ℕ} (L γ η : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop where
  /-- the labels of `α`-atoms lie in `[L⁻¹, L^{-γ+η}]`, `κ_v ∈ {0, 50}` -/
  labRange : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)
  kapVals : ∀ a ∈ M.atoms, (cls a).IsAlpha → (cls a).kap = 0 ∨ (cls a).kap = 50
  /-- each `ε`-atom is LG in the decoration -/
  epsLG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsEps →
    ∀ x y, M.atom x = a → M.atom y = a → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖
  /-- `|k_{ℓ₁} - k_{ℓ₂}| ∼ R_v` at an `α`-atom with two bonds -/
  alphaGap : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsAlpha → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    (cls a).lab / 2 ≤ ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ∧ ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ≤ 2 * (cls a).lab
  /-- an `α`-atom is an SG atom: its gap is not large (`≤ L^{-γ+η}`, DH23 Def 8.3; LG is the strict complement `>`) -/
  alphaSG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsAlpha → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ≤ L ^ (-γ + η)
  /-- (N1) every `β`-atom has a nonzero gap (L1874) -/
  betaGap : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsBeta → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    Molecule.gapAt L (0 : Mom d) κ x y ≠ 0
  /-- a vine component (two joints of degree `2`) is LG in the decoration; a double bond is vine (I) (L1806, second
  sentence of the cycle clause), included as the second disjunct -/
  vineLG : ((∃ j₁ j₂, M.IsVineEnl M.atoms j₁ j₂) ∨ (M.atoms.card = 2 ∧ ∀ a ∈ M.atoms, M.deg a = 2)) → ∀ κ, Adm κ →
    ∀ x y, M.atom x = M.atom y → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖
  /-- (N3) no `β`-cut with nonzero gap (L1887, "one cannot make any `β`-cuts in `𝕄₀`"; G3's `NoBetaCut` for nonzero-gap
  cuts): every cut of a vertex of degree `≥ 3` with nonzero gap `k_{x₁}-k_{x₂}` is an `α`-cut. It depends on the
  decoration through the gap, hence lives in `FinalDec`. -/
  noBetaCut : ∀ κ, Adm κ → ∀ v ∈ M.atoms, 3 ≤ M.deg v → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ →
    Molecule.gapAt L (0 : Mom d) κ x₁ x₂ ≠ 0 → M.IsAlphaCut v v₂ x₁ x₂
  /-- (N2) the `ι/κ` property of case (6) (L1895): two `α`-atoms `v₁ ≠ v₂` with `κ_{v₁}+κ_{v₂} = 0` and a `β`-atom `v₃`
  whose gaps `r₁, r₂, r₃` are nonzero with `±r₁ ± r₂ ± r₃ = 0` force `|r₃| ≳ L^{-50η} min(R₁,R₂)`. -/
  iota : ∀ κ, Adm κ → ∀ v₁ ∈ M.atoms, ∀ v₂ ∈ M.atoms, ∀ v₃ ∈ M.atoms, v₁ ≠ v₂ →
    (cls v₁).IsAlpha → (cls v₂).IsAlpha → (cls v₃).IsBeta → (cls v₁).kap + (cls v₂).kap = 0 →
    ∀ x₁ y₁ x₂ y₂ x₃ y₃, M.atom x₁ = v₁ → M.atom y₁ = v₁ → x₁ ≠ y₁ → M.atom x₂ = v₂ → M.atom y₂ = v₂ → x₂ ≠ y₂ →
      M.atom x₃ = v₃ → M.atom y₃ = v₃ → x₃ ≠ y₃ →
      Molecule.gapAt L (0 : Mom d) κ x₁ y₁ ≠ 0 → Molecule.gapAt L (0 : Mom d) κ x₂ y₂ ≠ 0 →
      Molecule.gapAt L (0 : Mom d) κ x₃ y₃ ≠ 0 →
      (∃ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
        Molecule.gapAt L (0 : Mom d) κ x₃ y₃ =
          s₁ • Molecule.gapAt L (0 : Mom d) κ x₁ y₁ + s₂ • Molecule.gapAt L (0 : Mom d) κ x₂ y₂) →
      L ^ (-50 * η) * min (cls v₁).lab (cls v₂).lab / 2 ≤ ‖Molecule.gapAt L (0 : Mom d) κ x₃ y₃‖


end WaveTurbulence.GammaLow.FinalCount.H
