/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Normalized
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepS10b
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr5
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10c
import Mathlib.Tactic
/-! # The vine-case and no-vine representation statements over `𝒱_γ` (packet L5a, interface of items G and J)

Main's assembly `Represents.stage1ReductionGate_of_vineCase` (`Stage1/Represents/RepS10e.lean`) consumes
`WTPrefix NoVineRepresentsAtN` (`RepPr7.noVine_prefixN`) and `WTPrefix VineCaseRepresents`
(`RepVD16.vineCase_prefix`, from the vine estimate). Their `𝒱_γ` forms, at `γ = P.γ ≤ 1/2`, over the producer's
pieces (`Represents.PcA P.γ`, the normalized piece of the representative prescribed point) are stated here; item G
proves them (`WTPrefix NoVineRepresentsLow`, `WTPrefix VineCaseRepresentsLow`) and item J consumes them. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Represents

variable [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact TVineIsoInvariant]

/-- **Vine case over `𝒱_γ`** (main's `Represents.VineCaseRepresents` at `γ = P.γ`): the `RepresentsInt` of the
producer's pieces whose representative prescription splices at least one unit. -/
def VineCaseRepresentsG (P : WTParams) [Fact (P.γ ≤ 1 / 2)] : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∀ π : Fama.Represents.PcA P.γ R p (objKind (2 * R)) A,
    unitBlocks P.γ (Fama.Represents.repPt P.γ π).prime.skeleton
      (VineA.PrescribedPrimeGarden.totalSigma P.γ (Fama.Represents.repPt P.γ π)) ≠ [] →
    Stage1PieceG.RepresentsInt (P := P) ((Fama.Represents.repPt P.γ π).normalizedPiece P.d) N tt base roots s
      (∑ LG ∈ Fama.Represents.membersP P.γ (Fama.Represents.clsP P.γ π), U.toLF.valueSel tt base roots LG
        (Fama.Represents.selP P.γ p (objKind (2 * R)) A P base roots π LG))

/-- The vine case at every `P` with `P.γ ≤ 1/2` (the `WTPrefix` target of item G). -/
def VineCaseRepresentsLow (P : WTParams) : Prop :=
  ∀ h : P.γ ≤ 1 / 2, @VineCaseRepresentsG _ _ _ P ⟨h⟩

/-- The no-vine case at every `P` with `P.γ ≤ 1/2` (`Fama.Represents.NoVineRepresentsAtN`, main's
`NoVineRepresentsAtN` over `𝒱_γ`; the `WTPrefix` target of item G, main's `noVine_prefixN`). -/
def NoVineRepresentsLow (P : WTParams) : Prop :=
  ∀ h : P.γ ≤ 1 / 2, @Fama.Represents.NoVineRepresentsAtN _ _ _ P ⟨h⟩

end WaveTurbulence.GammaLow.Fama
