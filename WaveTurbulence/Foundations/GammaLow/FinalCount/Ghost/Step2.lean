/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2G
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Triangle2
/-! **L6E GHOST, part 9: `UStep2.excess_low`**, the charged uniform Step 2 for every `0 < γ < 1`
(M1-R2 Theorem 6.1 at the triangle step `tri(P)`; §10.1).

Main's `FinalCountG3.UStep2.excess` (R38(2)) with its hypothesis `8η ≤ 2γ - 1` replaced by the transfer exponent
`ν ∈ {0, 1}`: the right-hand side `C · excessRHS(αnew, ΔF, ΔV_β) / ∏_{α-ghosts} T(Q_g, κ_g)` is multiplied by `L^{5ην}`;
`ν = 1` (an NC critical pair, the (f′) class NC) is unconditional; `ν = 0` needs `GhostPairsOK` for the triangle of the
step: every pair of `α`-ghosts is crit-free (a `κ = 50` ghost, or a label `< L^{-γ₀-4η}`) or transverse (`TRpair`).
Copy of main's proof (sha256 in COPIED-SHA256SUMS). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀}

/-- **The pairs of `α`-ghosts of a triangle step are crit-free or transverse** (the condition for `ν = 0`): for every two
distinct triangle atoms that are `α`-ghosts of `h`, `PairOK` with their labels `ghostQ`, `ghostK`, on the class `Adm0`. -/
def GhostPairsOK (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (h : HSt V D₀) (T : TriData h.s.M) :
    Prop :=
  ∀ j₁ j₂ : Fin 3, j₁ ≠ j₂ → (∃ R k, h.s.cls (T.t j₁) = .alpha R k) → (∃ R k, h.s.cls (T.t j₂) = .alpha R k) →
    PairOK T L γ η w (AdmS Adm0 h.s) j₁ j₂ (ghostQ h T j₁) (ghostQ h T j₂) (ghostK h T j₁) (ghostK h T j₂)

end WaveTurbulence.GammaLow.FinalCount.Ghost
