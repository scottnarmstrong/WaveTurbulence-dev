/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.LadFilt.FixedT
public import WaveTurbulence.Foundations.Flower.LadFilt.FiltL1

/-! # C3 LAD-FILT: the filtered ladder L¹ gate (o83 Theorem 8.3, E5 kernel-core form)

`ladderL1GateFilt : WTPrefix LadderL1AtFilt`. Parameters as in main's `ladderL1Gate` (Spine/LadderL1Gate), with the
window constant `τ★ + 1` (translated boxes reach one unit further) and `C₁ = ladConst d C₀`
(`C₀` replaced by `2 C₀ + 16·81^d` in main's formula). Proof: Lemma T (`filt_L1_le`) reduces the filtered sum to
the translated unfiltered cores, which `ladder_L1_fixed_T` bounds by the main ladder bound times
`ladderWt (δ L^{2γ}/2) τ ≤ ∏ (1 + |ξ_a|)²` (`ladderWt_filtShift_le`); the `ξ`-integral gives `∏ 𝔟(ψ_a)`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.WeylSums
  WaveTurbulence.Sumint MeasureTheory Set Finset

/-- **The filtered time-L¹ ladder gate** (S-MARKED §2.6, o83 Lemma T and Theorem K). -/
theorem ladderL1GateFilt : WTPrefix LadderL1AtFilt := by
  intro d hd γ hγ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hg1pos : 0 < g1 := by
    simp only [hg1]
    refine lt_min (by linarith) (lt_min one_pos ?_)
    nlinarith
  set η₀ : ℝ := min (min γ (1 - γ) / (10 * d)) ((g1 / 2) ^ 2) with hη₀
  have hη₀pos : 0 < η₀ := by
    refine lt_min ?_ (by positivity)
    apply div_pos (lt_min hγ0 (by linarith)) (by positivity)
  refine ⟨η₀, hη₀pos, ?_⟩
  intro η hη φin hφin τ hτ φ hφ
  obtain ⟨hη0, hηle⟩ := hη
  have hη1 : 10 * (d : ℝ) * η ≤ γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_left _ _)
  have hη2 : 10 * (d : ℝ) * η ≤ 1 - γ := by
    have h1 : η ≤ min γ (1 - γ) / (10 * d) := hηle.trans (min_le_left _ _)
    have h2 : 10 * (d : ℝ) * η ≤ min γ (1 - γ) := by
      rw [le_div_iff₀ (by positivity)] at h1; linarith
    exact h2.trans (min_le_right _ _)
  have hη2' : η < 1 - γ := by nlinarith
  have hη1' : η ≤ 1 := by nlinarith
  have hsq : Real.sqrt η ≤ g1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hηle.trans (min_le_right _ _)
  have hsqpos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  set x : ℝ := g1 - Real.sqrt η with hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x < 2 * γ := by
    have : g1 ≤ 2 * γ := min_le_left _ _
    linarith
  have hx2 : x ≤ 1 := by
    have : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hx3 : -2 * ((d : ℝ) - 1) * (1 - γ) + η ≤ -x := by
    have : g1 ≤ 2 * ((d : ℝ) - 1) * (1 - γ) := (min_le_right _ _).trans (min_le_right _ _)
    have hηsq : η ≤ Real.sqrt η := by
      have := Real.sqrt_le_sqrt hη1'
      nlinarith [Real.sq_sqrt hη0.le, Real.sqrt_nonneg η]
    linarith
  have hT1 : (0 : ℝ) < τ + 1 := by linarith
  obtain ⟨C0, hC0, hrt⟩ := rung_total hd ⟨hγ0, hγ1⟩ hη0 hη1 hη2 hT1 hx1 hx2 hx3
  refine ⟨ladConst d C0, one_le_ladConst d hC0, 1, one_pos, ?_⟩
  intro ν hν
  refine ⟨1, one_pos, ?_⟩
  intro δ hδ D hD hτD
  obtain ⟨L1, hL1, hL1'⟩ := hrt δ hδ.1 hδ.2
  obtain ⟨L2, hL2, hEnv⟩ := rung_env (T1 := τ + 1) (δ := δ) hγ0 hγ1 hη0 hη2' hx1
  refine ⟨1, le_rfl, max 2 (max L1 L2), le_max_left _ _, ?_⟩
  intro L hL
  have hLL1 : L1 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLL2 : L2 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL2' : 2 ≤ L := (le_max_left _ _).trans hL
  have hL1R : (1 : ℝ) ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x) := (hEnv L hLL2).1
  intro p hpD R hR1 hR2 G hplain hirr hbal hord1 hord2 Dd hDd hlayers m u v hm hlad hdisj
    base roots boundary T0 ψ Rv hRv hT0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlay : ∀ a, δ * ((Dd.layer a : ℝ) + 2) ≤ τ + 1 := by
    intro a
    have hpD' : p < D := hpD
    have h1 : Dd.layer a + 1 ≤ D := by have := hlayers a; omega
    have h2 : ((Dd.layer a : ℝ) + 1) ≤ (D : ℝ) := by exact_mod_cast h1
    have h3 : δ * ((Dd.layer a : ℝ) + 1) ≤ τ := by rw [hτD]; nlinarith [hδ.1]
    have h4 : δ ≤ 1 := hδ.2
    linarith
  have hc : 0 < δ * L ^ (2 * γ) := mul_pos hδ.1 (Real.rpow_pos_of_pos hL0 _)
  have hC1 := one_le_ladConst d hC0
  have hB00 : 0 ≤ ladConst d C0 * (ladConst d C0 * δ) ^ (n + 1) *
      L ^ (-x * (sourceLadderIncoherency G Dd.layer u v : ℝ) + 20 * (d : ℝ)) := by
    have := Real.rpow_pos_of_pos hL0 (-x * (sourceLadderIncoherency G Dd.layer u v : ℝ) + 20 * (d : ℝ))
    have : 0 ≤ ladConst d C0 := by linarith
    have : 0 ≤ δ := hδ.1.le
    positivity
  have hK : ∀ τ' : (Molecule.ladderAtoms u v) → ℝ,
      ‖(coupling d L γ δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
        ∫ t in timeBoxT G Dd.layer (Molecule.ladderAtoms u v) τ',
        ‖∑ z ∈ T0, ladderWeight Dd (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase Dd (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
        ladderWt (u := u) (v := v) (δ * L ^ (2 * γ) / 2) τ' *
          (ladConst d C0 * (ladConst d C0 * δ) ^ (n + 1) *
            L ^ (-x * (sourceLadderIncoherency G Dd.layer u v : ℝ) + 20 * (d : ℝ))) := fun τ' =>
    ladder_L1_fixed_T hd hγ0 hγ1 hx0 hx2 hC0 hδ.1 hδ.2 hL1R (hL1' L hLL1) hB hlad hplain Dd hDd hlay τ'
      base roots boundary T0 hT0
  have hmain := filt_L1_le ψ Dd (Molecule.ladderAtoms u v) L γ δ base Rv hRv hc T0 (fun z => z.1.1)
    (fun z => ladderWeight Dd (Molecule.ladderAtoms u v) L γ η base z.1.1)
    (‖(coupling d L γ δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1)) _ (by positivity) hB00
    (ladderWt (u := u) (v := v) (δ * L ^ (2 * γ) / 2)) hK
    (fun ξ => ladderWt_filtShift_le (gardenCtx hlad) hc Rv hRv ξ)
  have hprod : ∏ a ∈ Molecule.ladderAtoms u v, filterB ⇑(ψ a) ≤
      ∏ a ∈ Molecule.ladderAtoms u v, max 1 (filterB ⇑(ψ a)) :=
    Finset.prod_le_prod₀ (fun a _ => filterB_nonneg _) (fun a _ => le_max_right _ _)
  have hfin := hmain.trans (mul_le_mul_of_nonneg_right hprod hB00)
  refine hfin.trans (le_of_eq ?_)
  simp only [mul_assoc]
  rfl

end WaveTurbulence.Flower.LadFilt
