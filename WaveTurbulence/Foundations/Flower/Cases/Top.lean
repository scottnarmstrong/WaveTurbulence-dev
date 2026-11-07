/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Clauses3
/-! # The top theorem `layergardenFlower_v3_of_families` (PLAN §1.4). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set Filter Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

/-- Any prefix statement `Q` yields `Q` together with the fixed-parameter numerics, for large `L`. -/
theorem prefix_with_numerics (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Q : ℕ → WTParams → Prop} (H : WTPrefixP Q) :
    WTPrefixP fun Pm P => Q Pm P ∧ NumericsAll C U Pm P := by
  have H' := prefixP_small_moment H
    (fun _ m ν => min 1 (extractionDelta (2 * m) (ν / 3)))
    (fun _ m ν hν => lt_min zero_lt_one (extractionDelta_pos _ _))
  apply prefixP_late H'
  intro Pm _ P hP
  have hp0 := hP P.L le_rfl
  have hd3 : 3 ≤ P.d := hp0.2.2.1
  have hd : 1 ≤ P.d := by omega
  let X := 4 * (40 * P.d) ^ (2 * P.D + 2)
  have hcontrols : ∀ᶠ L : ℝ in atTop, ∀ p ∈ Finset.range P.D,
      ∀ N : ℕ, (N : ℝ) ≤ Real.log L ^ X →
        4 * ((2 * N + 1 : ℕ) : ℝ) ≤ L ∧
        C P.d * ((2 * N + 1 : ℕ) : ℝ) * U {P with L := 1} p *
          (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ (40 * P.d) ≤ L ^ (40 * P.d) ∧
        3 * (4 * Real.exp 1) * 4 ^ (40 * P.d) * C P.d * U {P with L := 1} p *
          ((2 * N + 1 : ℕ) : ℝ) ^ (40 * P.d + 2) ≤ L := by
    apply (eventually_all_finset _).mpr
    intro p _
    exact (eventually_extraction_controls (40 * P.d) X (by omega) (hC P.d).le
      (hU {P with L := 1} p).le).mono fun _ h => h.2
  filter_upwards [hcontrols, eventually_ge_atTop (max P.L 4),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with L hctrl hL hlog
  have hLP : P.L ≤ L := (le_max_left _ _).trans hL
  have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
  let P' : WTParams := {P with L := L}
  have hp' := hP L hLP
  have hδ : 0 < P'.δ := hp'.2.2.2.2.1
  have hν : 0 < P'.ν := hp'.2.2.2.1
  have hδ1 : P'.δ ≤ 1 := hp'.2.2.2.2.2.1.trans (min_le_left _ _)
  have hsm : P'.δ ≤ extractionDelta (2 * Pm) (P'.ν / 3) :=
    hp'.2.2.2.2.2.1.trans (min_le_right _ _)
  have hsmall0 := extractionDelta_bound hδ (by positivity : 0 < P'.ν / 3) (2 * Pm) hsm
  have e6 : 6 * (P'.ν / 3) = 2 * P'.ν := by ring
  rw [e6] at hsmall0
  refine ⟨hp'.1, ?_⟩
  intro p hpd N hN
  have hNlog : (N : ℝ) ≤ Real.log L ^ X := by
    apply (show (N : ℝ) ≤ (P'.N (p + 1) : ℝ) ^ 4 by exact_mod_cast hN).trans
    exact FC23.N_quartic_le_log_pow P' hd hlog (p + 1)
  obtain ⟨hA, hρ, hcost⟩ := hctrl p (Finset.mem_range.mpr hpd) N hNlog
  exact ⟨hd, hν, hδ, hδ1, hL4, hsmall0, hA, hρ, hcost⟩

/-- **`layergardenFlower_v3` from the two core families** (PLAN §1.4). -/
theorem layergardenFlower_v3_of_families (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ)
    (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    (hFilt : WTPrefixP (FlowerFiltFamilyAt C U))
    (hGain : WTPrefixP (FlowerGainFamilyAt C U)) : V2Chain.LayergardenFlowerV3Gate := by
  have hF := prefix_with_numerics C U hC hU hFilt
  have hG := prefix_with_numerics C U hC hU hGain
  have hPlain : WTPrefixP (FlowerCaseAt CasePlain) :=
    prefixP_map hF fun _ _ h => casePlain_of_filt C U hC hU h.1 h.2
  have hCut1 : WTPrefixP (FlowerCaseAt CaseCut1) :=
    prefixP_map hF fun _ _ h => cut1_clause_of_filt C U hC hU h.1 h.2
  have hCut2Zero : WTPrefixP (FlowerCaseAt CaseCut2Zero) :=
    prefixP_map hF fun _ _ h => cut2zero_clause_of_filt C U hC hU h.1 h.2
  have hNon : WTPrefixP (FlowerCasePatAt CaseCut2Pos PatNonplain) :=
    prefixP_map hF fun _ _ h => cut2pos_nonplain_of_filt C U hC hU h.1 h.2
  have hPl : WTPrefixP (FlowerCasePatAt CaseCut2Pos PatPlain) :=
    prefixP_map hG fun _ _ h => cut2pos_plain_of_gain C U hC hU h.1 h.2
  have hCut2 : WTPrefixP (FlowerCaseAt CaseCut2Pos) :=
    prefixP_map (prefixP_and hPl hNon
      (fun Pm => flowerCasePatAt_largeConstantMonotone _ _ Pm)
      (fun Pm => flowerCasePatAt_largeConstantMonotone _ _ Pm))
      fun _ _ h => caseAt_of_pat_split h.1 h.2
  exact layergardenFlower_v3_of_inputs hPlain hCut1 hCut2 hCut2Zero
    (coupleHalf_of_spine (Spine.stage1ReductionGate_of_V5' VineEst.vineEstCanonLayerHalfMK)
      WaveTurbulence.FinalCountAsm.finalCount_half)

end WaveTurbulence.Flower.Cases
