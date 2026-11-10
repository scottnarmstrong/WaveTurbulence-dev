/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepCountA` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.Statement
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.Shared.ClassCountStmt
public import WaveTurbulence.Foundations.Stage1.Represents.RepGateA
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepCountA
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# S2 REPRESENTS, VINE-F: the direct piece count (AMEND10, ruling R56) from CLASSCOUNT's garden count

TARGET L2251: the terms `K^eqc` are counted by gardens.  If every piece `π` has a representative layered garden
`rep π` (a Stage 1 carrier that carries a piece with the data `(ḡ, ρ̄)` of `π`, CLASSCOUNT's `HasPieceData`) and at most
`M` pieces share a representative, then the number of pieces with data `(g, r)` is at most `M` times CLASSCOUNT's garden
bound.  With `M = 3^N` (the prescriptions on the at most `N` groups of the representative's skeleton) this is the
clause of `Stage1CountsA`.
-/

@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.ClassCount WaveTurbulence.GammaLow.FinalCount

variable {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]



open Classical in
/-- Counting pieces through representatives with bounded fibres (main's `pieceCount_of_rep`, over L5c's class count
`ClassCountStmtG` and the `𝒱_γ` pieces `Stage1DataG`). -/
theorem pieceCount_of_rep (hcc : Famc.ClassCount.ClassCountStmtG) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ (P : WTParams) (hγ : P.γ ≤ 1 / 2), K ^ (P.D + 1) ≤ P.C₂ → ∀ p, p < P.D → ∀ R, 1 ≤ R →
      ∀ N, 1 ≤ N → ∀ (S : Stage1DataG P R) (rep : S.Pc → LayeredGarden (2 * R)) (M : ℕ),
        (∀ π, Stage1Carries P p N (rep π) ∧
          Famc.ClassCount.HasPieceDataG P.γ hγ P.d (rep π) (S.piece π).gbar (S.piece π).rbar) →
        (∀ LG, ((@univ S.Pc S.fin).filter fun π => rep π = LG).card ≤ M) →
        ∀ g r : ℕ,
          ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
            (M : ℝ) * ((C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
              P.C₂ ^ (g + r)) := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hγ hK p hp R hR N hN S rep M hrep hfib g r
  letI := S.fin
  set PS := (univ : Finset S.Pc).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r with hPS
  set A := PS.image rep with hA
  have hAc : (A.card : ℝ) ≤ (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
      P.C₂ ^ (g + r) := by
    refine hmain P hγ hK p hp R hR N hN g r A fun LG hLG => ?_
    obtain ⟨π, hπ, hLGe⟩ := Finset.mem_image.1 hLG
    have hgr := (Finset.mem_filter.1 hπ).2
    obtain ⟨h1, h2⟩ := hrep π
    rw [← hLGe]
    refine ⟨h1, ?_⟩
    rw [← hgr.1, ← hgr.2]
    exact h2
  have hcard : PS.card ≤ M * A.card := by
    have := Finset.card_le_mul_card_image PS M fun LG _ => by
      refine le_trans (Finset.card_le_card ?_) (hfib LG)
      intro π hπ
      simp only [Finset.mem_filter] at hπ ⊢
      exact ⟨Finset.mem_univ _, hπ.2⟩
    simpa [hA, mul_comm] using this
  have hcardR : (PS.card : ℝ) ≤ (M : ℝ) * (A.card : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _))

end WaveTurbulence.GammaLow.Fama.Represents
