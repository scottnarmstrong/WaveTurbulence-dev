/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.Cut1PrefixInterface
/-! Full frozen-prefix absorption of the local FC2 reduction. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Filter Induct

/-- Conditional cut1 theorem with the exact frozen quantifier order. Only
production of the explicitly budgeted FC3 uniform family is an analytic input. -/
theorem cut1_prefix_of_uniformFlowerFamily (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ)
    (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    (H : WTPrefixP (FC23UniformCut1At C U)) : WTPrefixP FC23Cut1At := by
  have H' := prefixP_small_moment H
    (fun _ m ν => min 1 (extractionDelta (2 * m) ν))
    (fun _ m ν _ => lt_min zero_lt_one (extractionDelta_pos (2 * m) ν))
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
  filter_upwards [hcontrols, eventually_ge_atTop P.L,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with L hctrl hL hlog
  let P' : WTParams := {P with L := L}
  have hp' := hP L hL
  have hδ : 0 < P'.δ := hp'.2.2.2.2.1
  have hν : 0 < P'.ν := hp'.2.2.2.1
  have hL2 : 2 ≤ P'.L := hp'.2.2.2.2.2.2
  have hδ1 : P'.δ ≤ 1 := hp'.2.2.2.2.2.1.trans (min_le_left _ _)
  have hsmall := extractionDelta_bound hδ hν (2 * Pm)
    (hp'.2.2.2.2.2.1.trans (min_le_right _ _))
  intro hγ p hpd R hR t ht s hs n n' ζ N hN kind pat dagger j
  have hNlog : (N : ℝ) ≤ Real.log L ^ X := by
    apply (show (N : ℝ) ≤ (P'.N (p + 1) : ℝ) ^ 4 by exact_mod_cast hN).trans
    exact N_quartic_le_log_pow P' hd hlog (p + 1)
  obtain ⟨hA, hρ, hcost⟩ := hctrl p (Finset.mem_range.mpr hpd) N hNlog
  have hfamily (j : ℕ) := uniformFlowerFamily_clip P' R p N kind pat dagger ζ t s n n' _ _ _ _
    (hp'.1 hγ p hpd R hR t ht s hs n n' ζ N hN kind pat dagger j)
  have hL1 : 1 ≤ P'.L := (by norm_num : (1 : ℝ) ≤ 2).trans hL2
  have hsum := summable_clipped_inputs P' R p hpd.le hd hL1 hR
  have hroot : 0 ≤ flowerRootBudget Pm P' p ζ n n' := by
    unfold flowerRootBudget
    exact Real.rpow_nonneg (by unfold jbr; positivity) _
  have hh := cut1_scale_bound P' (inputsF P' (clipRemainder p R)) p N kind pat dagger ζ t s n n'
    (40 * P'.d) (C P'.d) (U {P' with L := 1} p) (flowerRootBudget Pm P' p ζ n n')
    (flowerLExponent Pm P' pat) (hC _) (hU _ _) hL1 hδ hδ1 hν.le hroot hsmall
    hA hρ hcost hsum hfamily j
  rw [flowerSumP_cut1_clip] at hh
  have he : (((40 * P'.d) * (2 * Pm) : ℕ) : ℝ) = 80 * P'.d * Pm := by push_cast; ring
  simpa only [flowerRootBudget, flowerLExponent, he] using hh
end WaveTurbulence.FC23
