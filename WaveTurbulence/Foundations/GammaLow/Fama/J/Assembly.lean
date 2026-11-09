/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.J.Counts
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr3
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr8
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr9
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepCnt2
public import WaveTurbulence.Foundations.GammaLow.Famc.Subpro.Gate
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10e
import Mathlib.Tactic
/-! # Assembly of the Stage 1 reduction gate for `γ ≤ 1/2` (packet L5a, item J)

Main's `Represents.stage1ReductionAt_of_inputs` (`RepS10c`) and `Represents.stage1ReductionGate_of_vineCase`
(`RepS10e`) over `𝒱_γ`: the producer `prodData` (pieces = normalized pieces of the representative prescribed points),
its partition (`stage1Partition_prod`), soundness (`normalizedPiece_sound`, with L5c's subpro′
`Famc.Subpro.normalizedSubpro`), the order bound, the counts (`prod_stage1Counts`, from L5c's class count), and the
representation of every piece: no-vine pieces by `NoVineRepresentsLow`, vine pieces by `VineCaseRepresentsLow`
(item G). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Fama
open scoped Classical
open Finset Set WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.GammaLow.Fama.Represents

/-- **The Stage 1 reduction at `P` (`P.γ ≤ 1/2`) from the class count and the two representation statements**
(main's `stage1ReductionAt_of_inputs` over `𝒱_γ`). -/
theorem stage1ReductionGammaAt_of_inputs (hcc : Famc.ClassCount.ClassCountStmtG) :
    ∃ C₀ K : ℕ, 2 ≤ C₀ ∧ ∀ P : WTParams, P.γ ≤ 1 / 2 → (K : ℝ) ^ (P.D + 1) ≤ P.C₂ → 2 ≤ P.L →
      NoVineRepresentsLow P → VineCaseRepresentsLow P → Stage1ReductionGammaAt C₀ P := by
  obtain ⟨C₀, K, hC₀, hcnt⟩ := prod_stage1Counts hcc
  refine ⟨C₀, K, hC₀, ?_⟩
  intro P hγ hK hL hnv0 hvine0
  haveI : Fact (P.γ ≤ 1 / 2) := ⟨hγ⟩
  have hnv := hnv0 hγ
  have hvine := hvine0 hγ
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize
  have hplain : ∀ LG ∈ A, LG.garden.IsPlain := fun LG hLG => (hA LG hLG).1.1
  set kind := WaveTurbulence.Represents.objKind (2 * R) with hkind
  have hctrl := WaveTurbulence.Represents.controlled_of_bounded hA U hb
  refine ⟨prodData P p kind A (fun π => ∑ LG ∈ membersP P.γ (clsP P.γ π), U.toLF.valueSel tt base roots LG
      (selP P.γ p kind A P base roots π LG)), ClA P.γ R p kind A, inferInstance, clsP P.γ, membersP P.γ,
    selP P.γ p kind A P base roots, stage1Partition_prod p kind A hplain P base roots, ?_, ?_, ?_,
    hcnt P (by exact_mod_cast hK) p hp R hR N hN1 kind A hA _⟩
  · intro π
    refine ⟨rfl, ?_⟩
    by_cases hv : unitBlocks P.γ (repPt P.γ π).prime.skeleton
        (VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π)) = []
    · have hc := hA _ (repPt_layered_mem π)
      have h1 := noVine_representsIntA P hnv (repPt P.γ π) hv hp hN
        hc.2.2.1 hc.1 tt htt U.toLF (hctrl _ (repPt_layered_mem π)) base roots s
        (hsize _ (repPt_layered_mem π))
      have h2 := noVine_members_sum P base roots tt U.toLF π hv
      have h3 : Stage1PieceG.RepresentsInt (P := P) ((repPt P.γ π).normalizedPiece P.d) N tt base roots s
          (∑ LG ∈ membersP P.γ (clsP P.γ π), U.toLF.valueSel tt base roots LG
            (selP P.γ p kind A P base roots π LG)) := by
        rw [h2]
        exact h1
      exact h3
    · exact hvine p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize π hv
  · intro π
    exact normalizedPiece_sound Famc.Subpro.normalizedSubpro P hR (repPt P.γ π) (hA _ (repPt_layered_mem π)) hN
      (by linarith) base roots
  · intro π
    have h := prod_piece_gsb_order P p N kind A hA π
    have h3 := order_add_hinges_le (γ := P.γ) (Mole.garden_isMolecule (repPt P.γ π).prime.skeleton)
      (VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π))
    show (stSt P.γ (repPt P.γ π).prime.skeleton (VineA.PrescribedPrimeGarden.totalSigma P.γ (repPt P.γ π))).G.order ≤ N
    omega

/-- **The Stage 1 reduction gate for `γ ≤ 1/2`** from the class count over `𝒱_γ` (L5c, item I) and the no-vine and
vine-case representation statements (item G), with their large-constant monotonicity (main's
`stage1ReductionGate_of_vineCase`). -/
theorem stage1ReductionGateLow_of (hcc : Famc.ClassCount.ClassCountStmtG)
    (hnv : WTPrefix NoVineRepresentsLow) (hvine : WTPrefix VineCaseRepresentsLow)
    (hnvm : LargeConstantMonotone NoVineRepresentsLow) (hvm : LargeConstantMonotone VineCaseRepresentsLow) :
    Stage1ReductionGateLow := by
  obtain ⟨C₀, K, hC₀, hmain⟩ := stage1ReductionGammaAt_of_inputs hcc
  refine ⟨fun _ _ => C₀, fun _ _ => hC₀, ?_⟩
  have hQ := prefix_and hnv hvine hnvm hvm
  have hQ2 := WaveTurbulence.Represents.prefix_with_C2_ge hQ (hnvm.and hvm) (K : ℝ)
  exact prefix_map (fun P hP hγ => hmain P hγ hP.2.1 hP.2.2 hP.1.1 hP.1.2) hQ2

end WaveTurbulence.GammaLow.Fama
