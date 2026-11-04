/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceStaticBlockReduction
public import WaveTurbulence.Foundations.Sumint.SourceAllEnvelopeBlocks
public import WaveTurbulence.Foundations.Sumint.BlockBudgetRecombination

/-!
# The actual localized source static integral satisfies the Step 2 power bound

Every pair envelope and block budget is supplied by the proved source
window estimates. The external case-(b) norm power and literal source
weight multiplicity are included. The constant precedes delta and
Dsteps; the later lattice threshold is uniform in the datum, its size,
all spatial centres, and every Fourier modulation.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 2: actual static-domain power bound with all bad, weight, and incoherent gains. -/
theorem exists_source_static_power_bound (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : 0 < η) (hηbase : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (hs : Real.sqrt η ≤ gammaBase γ/8) (hγη : γ+η ≤ 1)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβpair : β/2 < 2*γ) (hβweyl : β/2 < 2*((d:ℝ)-1)*(1-γ)-η)
    (hβnormal : β < 20*γ) (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ t c : ℝ,
      ENNReal.ofReal (L^(-(gammaWeight d γ-Real.sqrt η)*(D.M₁:ℝ)))*
        (ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
          (∫⁻ τ in Icc (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β))) ∩ staticTimeDomain D,
            ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ)) ≤
      ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
        L^((D.S.M:ℝ)*((d:ℝ)-γ)-
          (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
          (β/20)*(D.M₀:ℝ))) := by
  obtain ⟨C,CsA,CmA,CsC,CmC,hC,hCsA,hCmA,hCsC,hCmC,hstatic⟩ :=
    exists_source_static_block_reduction d hd γ hγ η hη (by linarith only [hηsmall])
      τstar hτstar β hβ hβpair hβweyl
  obtain ⟨G,hG,hblock⟩ := exists_source_all_envelope_block_bounds d hd hγ hηbase hηsmall
    τstar hτstar β hβ hβnormal hhigh C CsA CmA CsC CmC hCsA hCmA hCsC hCmC
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨RS,hRS,hS⟩ := hstatic δ N ⟨hδ.1,by linarith [hδ.2]⟩ hτ
  obtain ⟨RB,hRB,hB⟩ := hblock δ hδ
  refine ⟨max RS RB,hRS.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r hr hrupper t c
  have hLRS : RS ≤ L := (le_max_left _ _).trans hL
  have hLRB : RB ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith [hRS.trans hLRS]
  let F (i : Fin D.S.I) :=
    (caseBMultiplier D r i*linearFactorMass D L γ δ p ν r t c (L^(-β)) i)*
      (∏ j : Fin (D.S.m i), sourcePairEnvelope D L γ δ η β τstar C CsA CmA CsC CmC ⟨i,j⟩)*
      normalMassInBlock D.S (normalFactorMass D L γ δ p ν r t
        (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β)))) i
  have hmass : ENNReal.ofReal (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)*
      (∫⁻ τ in Icc (enlargedTimeLower D c (L^(-β))) (enlargedTimeUpper D c (L^(-β))) ∩ staticTimeDomain D,
        ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ₑ) ≤ ∏ i, F i := by
    have hb := mul_le_mul' (le_refl (ENNReal.ofReal
      (‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card)))
      (hS L hLRS D A hD p ν r t c)
    rw [case_b_norm_mul_block_product] at hb
    exact hb
  have hbudget := block_budget_recombination D hD (by omega : 2 ≤ d) hγ hs hL1 hδ.1
    (zero_le_one.trans hG) F (fun i => hB L hLRB D N hτ A hD hγη p ν r hr hrupper t c i)
  exact (mul_le_mul' le_rfl hmass).trans hbudget

end WaveTurbulence.Sumint
