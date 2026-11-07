/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFinal3

/-! # P4-W2 (session 20): `uniformTermCertAt_rec` and `uniformTermCertK` (all kinds, no staging hypothesis) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal


open Classical in
/-- **`UniformTermCertAtK` for all kinds** (the dispatches `DispK01`, `DispK2` at the clock radius `D` and one constant `K0`). -/
theorem uniformTermCertAt_rec {Pe : WTParams} (hPe : AmbP 6561 Pe) (hL2 : 2 ≤ Pe.L) (hηγ : Pe.η ≤ Pe.γ)
    (hw : 0 ≤ Pe.gamma1 - Real.sqrt Pe.η)
    {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤) (hbody : TermRecBody (A := 6561) Pe.d Pe.η C)
    {K0 : ℝ≥0∞} (hK0t : K0 ≠ ⊤) (hdisp : DispK01.{0} Pe K0) (hd2 : DispK2.{0} Pe (Pe.D : ℝ) K0)
    (cf Kr Kb Km : ℝ) (hcf : C.toReal ≤ cf) (hKr : cf * 2 * (rowCb Pe * Pe.C₁ ^ 2) ≤ Kr) (hKr1 : 1 ≤ Kr)
    (hKb : (Kall Pe.d (K0 * ENNReal.ofReal (K2.KxX Pe.η))).toReal * (4 * TR Pe.η ^ 2 * trC (6 * Pe.η ^ 6) ^ 2 / rowCb Pe ^ 2) ≤ Kb) (hKb1 : 1 ≤ Kb)
    (hKm1 : 1 ≤ Km) (hKm : 3 * max (tcSq Pe.η) 1 ≤ Km) :
    WaveTurbulence.VineEstS5C.P4.Final.UniformTermCertAtK 6561 Pe Km Kr Kb := by
  unfold WaveTurbulence.VineEstS5C.P4.Final.UniformTermCertAtK
  intro p h B₀ wBar hB₀ E hinc w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre lam hR hcoh
  have hall := term_rec_exists hPe hL2 hηγ hw hC1 hCt hbody hK0t hdisp hd2 cf Kr Kb Km hcf hKr hKr1 hKb hKb1 hKm1 hKm h B₀ wBar hB₀ E hinc
    hprime hM9 B RD hG layer hLayer hcan hlay hord hl1 centre lam hR hcoh
  have hL0 : 0 < Pe.L := by linarith
  have hδ : 0 < Pe.δ := hPe.hδ
  have hc : ((coupling Pe.d Pe.L Pe.γ Pe.δ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < coupling Pe.d Pe.L Pe.γ Pe.δ := by unfold coupling; positivity
    exact_mod_cast this.ne'
  have hζ0 : clLocalZeta R ≠ 0 := by
    intro h0
    have := norm_clLocalZeta R
    rw [h0, norm_zero] at this
    norm_num at this
  set N : ℝ≥0∞ := ‖(coupling Pe.d Pe.L Pe.γ Pe.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R‖ₑ with hN
  have hN0 : N ≠ 0 := (enorm_ne_zero).2 (mul_ne_zero (pow_ne_zero _ hc) hζ0)
  have hNt : N ≠ ⊤ := enorm_ne_top
  set lit : ℝ≥0∞ := ENNReal.ofReal ((1 + |lam|) ^ (6 * Pe.η ^ 6) * ((engNs Pe.η Pe.C₁ Km Kr * Real.sqrt Pe.δ) ^ clLocalOrder2 RD hG R *
            (Kb ^ (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card *
            Pe.L ^ (-(Pe.η ^ 8 * ((cohmolIndex B RD hG layer +
              (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
              Pe.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + Pe.η ^ 7)) *
            regionLeafSize RD hG R layer hLayer (fun _ => B₀))) with hlit
  refine ⟨lit / N, fun ψ hψ => ?_, ?_⟩
  · obtain ⟨q, hq, hbound⟩ := hall ψ hψ
    refine hq (lit / N) ?_
    refine (ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl hNt)).2 ?_
    rw [mul_comm]; exact hbound
  · exact ENNReal.mul_div_le

open Classical in
/-- **`UniformTermCertTargetK`** (TARGET `UniformTermCertAtK`, every kind). -/
theorem uniformTermCertK :
    WaveTurbulence.VineEstS5C.P4.Final.UniformTermCertTargetK := by
  intro d hd γ hγ
  have hd1 : 1 ≤ d := by omega
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hg1pos : 0 < g1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 < 2 * γ := by linarith [hγ.1]
    have h2 : 0 < 2 * ((d : ℝ) - 1) * (1 - γ) := by
      have : 0 < 1 - γ := by linarith [hγ.2]
      have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
      positivity
    exact lt_min h1 (lt_min one_pos h2)
  refine ⟨min γ (g1 ^ 2), lt_min hγ.1 (by positivity), fun η hη φin hφin τstar hτ φ hsol c0 hc0 => ?_⟩
  have hηγ : η ≤ γ := hη.2.trans (min_le_left _ _)
  have hηg : η ≤ g1 ^ 2 := hη.2.trans (min_le_right _ _)
  have hsq : Real.sqrt η ≤ g1 := by
    calc Real.sqrt η ≤ Real.sqrt (g1 ^ 2) := Real.sqrt_le_sqrt hηg
      _ = g1 := Real.sqrt_sq hg1pos.le
  obtain ⟨C, hC1, hCt, hbody⟩ := termCertWG_rec (A := 6561) d η hd1
  let P₀ : WTParams := ⟨d, γ, η, φin, τstar, φ, c0, 0, 1, 0, 0, 2⟩
  obtain ⟨K00, hK00t, hK001, hdisp0⟩ := dispK01_uniform.{0} (A := 6561) P₀
  set cf : ℝ := max C.toReal 1 with hcf
  set Kr : ℝ := max 1 (cf * 2 * (rowCb P₀ * c0 ^ 2)) with hKr
  refine ⟨3 * max (tcSq η) 1, Kr, ?_, le_max_left _ _, fun ν δ D hδ hτD => ?_⟩
  swap
  · obtain ⟨K02, hK02t, hK021, hdisp2⟩ := dispK2_uniform.{0} (A := 6561) P₀ (D : ℝ)
    set K0 : ℝ≥0∞ := K00 ⊔ K02 with hK0def
    have hK0t : K0 ≠ ⊤ := (max_lt (lt_top_iff_ne_top.2 hK00t) (lt_top_iff_ne_top.2 hK02t)).ne
    set Kb : ℝ := max 1 ((Kall d (K0 * ENNReal.ofReal (K2.KxX η))).toReal * (4 * TR η ^ 2 * trC (6 * η ^ 6) ^ 2 / rowCb P₀ ^ 2)) with hKb
    refine ⟨Kb, le_max_left _ _, fun C₂ L hL hamb => ?_⟩
    have hPe : WaveTurbulence.VineEstS5C.P2.AmbP 6561 (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) := hamb
    exact @uniformTermCertAt_rec (⟨d, γ, η, φin, τstar, φ, c0, ν, δ, D, C₂, L⟩ : WTParams) hPe hL hηγ
      (by show 0 ≤ g1 - Real.sqrt η; linarith) C hC1 hCt hbody K0 hK0t
      (DispK01.mono (hdisp0 ν δ D C₂ L hamb) le_sup_left) (DispK2.mono (hdisp2 ν δ D C₂ L hamb) le_sup_right)
      cf Kr Kb (3 * max (tcSq η) 1)
      (le_max_left _ _) (le_max_right _ _) (le_max_left _ _) (le_max_right _ _) (le_max_left _ _)
      (by have : (1 : ℝ) ≤ max (tcSq η) 1 := le_max_right _ _
          linarith)
      le_rfl
  · have : (1 : ℝ) ≤ max (tcSq η) 1 := le_max_right _ _
    linarith

end WaveTurbulence.VineEstS5C.P4.W2
