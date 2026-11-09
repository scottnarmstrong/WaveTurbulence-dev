/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Op1Cone5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
public import WaveTurbulence.Foundations.FinalCount.G3Iota
public import WaveTurbulence.Foundations.FinalCount.VCSource
/-! **Ghost assembly: the interface of `ChainCoverLow'` (ruling R194)** (design: `CHAIN-DESIGN.md`).

* `Ex1Cone`: the Op-1 creation cone in the run's uniform-step form — the binders of H-ASM's `Ex1A`
  (`H/FinalCount/AsmPhase1b.lean`) at `kp = 0` and `ΔF = 0`, with a critical label, the joint cone `JointCone` on the
  inherited class and `k ≤ 2`; right side `CA · (3·5^d·L^{-5ηk}) · excessRHS [(R,0),(R,0)] 0 0`. H-ASM produces it
  from `Ghost.prop94_vine_all_family_cone` (Theorem C unconditional) exactly as it produces `Ex1A` from
  `prop94_vine_all_gamma`, with `CA` the larger of the two `Cs`-constants.
* `splitK = 18`: the number of classes of the (f′) split at one creation step (with adjacency: per new critical atom
  "transverse to its old critical neighbours" or "in the cone of one of them" (≤ 3), times "transverse/relative cone"
  between the two new atoms of an Op-2 step (≤ 2): `3 · 3 · 2`). It enters the budgets `hNC1'`, `hNC2'` as an explicit
  factor (the cover engine weighs a node's children by `1/(splitK·N)` and its final part by `1/N`, so the conclusion
  keeps `N^4`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The number of classes of the (f′) split at one creation step. -/
def splitK : ℕ := 18

/-- **The Op-1 creation cone, uniform-step form** (input of `ChainCoverLow'`; produced by H-ASM from
`prop94_vine_all_family_cone`). -/
def Ex1Cone (L γ η δ C₁ : ℝ) (w : Mom d) (M₀ : Molecule V D₀) (P : Finset V → ℝ) (CA : ℝ) : Prop :=
  ∀ (Adm0 : (D₀ → (Fin d → ℤ)) → Prop), (∃ k0, Adm0 k0) → (∀ k0, Adm0 k0 → SourceLadderGaps M₀ L w P k0) →
    (∀ k0, Adm0 k0 → ∃ c0, M₀.IsDecoration L w c0 k0 ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
    ∀ {h h' : HSt V D₀}, H.UStep1 L γ η w Adm0 h h' → LCtx M₀ h.s → AtomRelU Adm0 L w h → h.s.M.IsMolecule →
      ∃ (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePostL K R kp ∧
        ((Step1.SingleVineVCGamma K ∨ Nonempty (Step1.DoubleShape K)) →
        K.post.numComponents ≤ h.s.M.numComponents → kp = 0 → Crit L γ η R →
        JointCone K L γ δ η w (AdmS Adm0 h.s) → ∀ k : ℕ, k ≤ 2 →
          IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
            (ENNReal.ofReal (CA * (3 * 5 ^ d * L ^ (-5 * η * (k : ℝ))) * excessRHS L γ η [(R, 0), (R, 0)] 0 0)))

end WaveTurbulence.GammaLow.FinalCount.Ghost
