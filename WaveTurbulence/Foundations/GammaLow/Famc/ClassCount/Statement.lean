/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
public import WaveTurbulence.Foundations.Stage1.Shared.ClassCountStmt
/-! # The Stage 1 class count over `𝒱_γ`: the statement (packet L5c, item I taken over from L5a)

TARGET (finalprooffin), L2241–L2252, for the `𝒱_γ` Stage 1 pieces of L5a's construction (`Fama.stage1PieceOf`):
main's `ClassCount.HasPieceData` / `ClassCountStmt` (Stage1/Shared/ClassCountStmt.lean) verbatim, with main's
`RedSplice.stage1PieceOf` replaced by `Fama.stage1PieceOf P.γ` (for `P.γ ≤ 1/2`; the instance `Fact (γ ≤ 1/2)` is built
from the hypothesis). Consumed by L5a's assembly (item J) where main's `Represents.prod_stage1Counts` consumes
`ClassCountStmt`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RedSplice

/-- The layered garden `LG` carries a `𝒱_γ` Stage 1 piece `Fama.stage1PieceOf γ d hS LG hd σ` with data
`(ḡ, ρ̄) = (g, r)`: for some skeleton `S`, replacement data `D` decoding `LG`, and prescription `σ` (main's
`ClassCount.HasPieceData`). -/
def HasPieceDataG [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] (γ : ℝ) (hγ : γ ≤ 1 / 2) (d : ℕ)
    {R : ℕ} (LG : LayeredGarden (2 * R)) (g r : ℕ) : Prop :=
  haveI : Fact (γ ≤ 1 / 2) := ⟨hγ⟩
  ∃ (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (σ : Prescription S),
    (Fama.stage1PieceOf γ d hS LG hd σ).gbar = g ∧ (Fama.stage1PieceOf γ d hS LG hd σ).rbar = r

/-- **The class count over `𝒱_γ` (TARGET finalprooffin, L2236–L2252), garden form** (main's `ClassCountStmt` with
`HasPieceDataG`, for `P.γ ≤ 1/2`). -/
def ClassCountStmtG [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] : Prop :=
  ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, ∀ hγ : P.γ ≤ 1 / 2, K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D →
    ∀ R, 1 ≤ R → ∀ N, 1 ≤ N → ∀ g r : ℕ, ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, Stage1Carries P p N LG ∧ HasPieceDataG P.γ hγ P.d LG g r) →
      (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
        P.C₂ ^ (g + r)

end WaveTurbulence.GammaLow.Famc.ClassCount
