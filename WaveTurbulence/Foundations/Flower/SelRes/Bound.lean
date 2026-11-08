/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Point
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Spine.PieceArithmetic

/-! # D7 SEL-RES / Bound: `MarkedPieceBoundSelAtT` and `MarkedPieceBoundSelAt` (C5 target 1′, R175, F-C5b-1)

C5a's `markedPieceBoundAt_of_one_le_d` with the pointwise bound `point_bound_atom`, integrated against
`‖w‖ ∏(1+|ξ_v|)^{1/18}` (`RepresentsIntMKSel`'s mass). The selected factors combine as
`L^{7(47d+2)a} · L^{(71d−14)a} = L^{400d·a}`, times `∏_{v ∈ sel} Ms(v.1.1)^{-1/18}` (per-tree scales). The single-scale
`markedPieceBoundSelAt_of_one_le_d` is the case `Ms ≡ M₂`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.FinalMKPiece

theorem prod_sel_factor_atom {ι : Type*} (s : Finset ι) {L : ℝ} (hL : 0 < L) (M : ι → ℝ) (κ : ℝ) (w : ι → ℝ) :
    ∏ v ∈ s, (L ^ κ * M v ^ (-(1 / 18 : ℝ)) * w v) =
      L ^ (κ * (s.card : ℝ)) * (∏ v ∈ s, M v ^ (-(1 / 18 : ℝ))) * ∏ v ∈ s, w v := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_mul_natCast hL.le]

/-- **The selected piece bound with per-tree scales** (o73 Prop 20.1, finding F-C5b-1), for `1 ≤ d`. -/
theorem markedPieceBoundSelAtT_of_one_le_d {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (_hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P) :
    MarkedPieceBoundSelAtT cP cθ P := by
  intro p R n hp hR hRmax π sel Ms hM hsel hone tt base roots hπ hnsb hnL val s hs0 hval
  obtain ⟨Ξ, _, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwbound, hD⟩ := hval
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hMs0 : 0 ≤ ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) :=
    Finset.prod_nonneg fun v hv => Real.rpow_nonneg (by linarith [hM v hv]) _
  have hC2 : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
  set a : ℝ := (sel.card : ℝ) with ha
  set M : ℝ := P.C₂ * Real.exp ((π.Gsb.order : ℝ) * (Real.log P.C₁ + 10 * P.ν * Real.log P.δ) +
        (-40 * P.ν * P.η * (π.gsb : ℝ) -
          P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 2 -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * Real.log P.L) with hMdef
  set cq : ℝ := cθ ^ (40 * P.ν) with hcq
  set Ek : ℝ := (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ) with hEk
  set a0 : ℝ := cP * P.d * (π.nProt : ℝ) with ha0
  set Gsel : ℝ := P.L ^ ((71 * (P.d : ℝ) - 14) * a) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) with hGsel
  set Wf : Ξ → ℝ := fun ξ => ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) with hWf
  have hcq1 : 1 ≤ cq := Real.one_le_rpow hcθ (by have := hs.nu_pos; linarith)
  have hM0' : 0 ≤ M := by rw [hMdef]; exact mul_nonneg hC2 (Real.exp_pos _).le
  have hG0 : 0 ≤ Gsel := by positivity
  have hbsf : bsf P cθ π = M * cq ^ π.Gsb.order * P.L ^ Ek := rfl
  -- the pointwise bound
  have hKle : ∀ ξ, ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) * Wf ξ := by
    intro ξ
    have := point_bound_atom hs hd hcθ hcoarse hfine hp hR hRmax π base roots hπ hnsb hnL tt (ctr ξ) (edge ξ)
      (hinge ξ) (freq ξ) (hD ξ) sel (fun v => Ms v.1.1) hM hsel hone
    rw [prod_sel_factor_atom sel hL0] at this
    refine this.trans (le_of_eq ?_)
    rw [hbsf, hGsel, hWf]; ring
  have hMt0 : 0 ≤ M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel := by positivity
  have hpt : ∀ ξ, ‖w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots‖ ≤ ‖w ξ‖ * Wf ξ * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by
    intro ξ
    rw [norm_mul]
    calc ‖w ξ‖ * ‖splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
          P.L P.γ P.η P.δ base roots‖ ≤ ‖w ξ‖ * ((M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) * Wf ξ) :=
          mul_le_mul_of_nonneg_left (hKle ξ) (norm_nonneg _)
      _ = ‖w ξ‖ * Wf ξ * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by ring
  have hnorm : ‖val‖ ≤ (∫ ξ, ‖w ξ‖ * Wf ξ ∂μ) * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := by
    rw [hv]
    have h := norm_integral_le_of_norm_le (hwint.mul_const (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel))
      (Filter.Eventually.of_forall hpt)
    simpa only [integral_mul_const] using h
  set W : ℝ := ∫ ξ, ‖w ξ‖ * Wf ξ ∂μ with hW
  have hW0 : 0 ≤ W := integral_nonneg fun ξ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (by linarith [abs_nonneg (freq ξ v)]) _)
  set Ls : ℝ := P.L ^ (7 * (47 * P.d + 2) * a) with hLs
  have hLa : 0 < P.L ^ a0 := Real.rpow_pos_of_pos hL0 _
  have hLs0 : 0 < Ls := Real.rpow_pos_of_pos hL0 _
  have hden : 0 < s * P.L ^ a0 * Ls := by positivity
  set W' : ℝ := W / (s * P.L ^ a0 * Ls) with hW'
  have hW'0 : 0 ≤ W' := div_nonneg hW0 hden.le
  have hwb : W' ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := by
    rw [hW', div_le_iff₀ hden]
    calc W ≤ _ := hwbound
      _ = _ := by ring
  have hcls := class_piece_bound (C := P.C₁) (δ := P.δ) (L := P.L) (η := P.η) (ν := P.ν)
    (n := n) (nsb := π.Gsb.order) (R := R) (m := π.Gsb.order + 2 * R) (W := W') (X := M) (H := P.C₂)
    (gsk := (π.gsk : ℝ)) (bsk := (π.bsk : ℝ)) (qsk := (π.Cs.hinges.card : ℝ))
    (gsb := (π.gsb : ℝ)) (ρsb := (π.Gsb.molecule.rho : ℝ))
    hs.c1_ge hs.delta_pos hs.delta_le hL1 hs.nu_pos (by linarith [hs.nu_small]) hs.nu_eta
    hs.eta_pos hs.eta_le hnsb (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC2 hW'0 hM0' hwb (by rw [hMdef])
  have hcqn : cq ^ π.Gsb.order ≤ cq ^ n := pow_le_pow_right₀ hcq1 hnsb
  have hWeq : W = W' * (s * P.L ^ a0 * Ls) := by rw [hW']; field_simp
  have hT0 : 0 ≤ P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) := by
    have := hs.c1_ge; have := hs.delta_pos; positivity
  have hmext : P.L ^ markedExtra cP π = P.L ^ a0 * P.L ^ Ek := by
    rw [← Real.rpow_add hL0]; congr 1; unfold markedExtra; simp only [ha0, hEk]; ring
  have hsel400 : Ls * Gsel = P.L ^ (400 * (P.d : ℝ) * a) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ)) := by
    rw [hLs, hGsel, ← mul_assoc, ← Real.rpow_add hL0]; congr 2; ring
  calc ‖val‖ ≤ W * (M * cq ^ π.Gsb.order * P.L ^ Ek * Gsel) := hnorm
    _ = s * P.L ^ a0 * P.L ^ Ek * cq ^ π.Gsb.order * (W' * M) * (Ls * Gsel) := by rw [hWeq]; ring
    _ ≤ s * P.L ^ a0 * P.L ^ Ek * cq ^ n *
        (P.C₂ * (P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
      P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
      P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) * (Ls * Gsel) := by
        gcongr
    _ = _ := by rw [hmext, hsel400, mul_pow, mul_pow, hcq]; ring

/-- **The selected piece bound** (o73 Prop 20.1), for `1 ≤ d`: `markedPieceBoundSelAtT_of_one_le_d` at `Ms ≡ M₂`. -/
theorem markedPieceBoundSelAt_of_one_le_d {P : WTParams} (hd : 1 ≤ P.d) (hs : PieceSmall P) {cP cθ : ℝ}
    (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) (hcoarse : CoarseSplicedAtMK P) (hfine : FineSplicedAtMK P) :
    MarkedPieceBoundSelAt cP cθ P := by
  intro p R n hp hR hRmax π sel M₂ hM hsel hone tt base roots hπ hnsb hnL val s hs0 hval
  have hM0 : 0 < M₂ := by linarith [hs.L_ge]
  have h := markedPieceBoundSelAtT_of_one_le_d hd hs hcP hcθ hcoarse hfine hp hR hRmax π sel (fun _ => M₂)
    (fun _ _ => hM) hsel hone tt base roots hπ hnsb hnL val s hs0 hval
  have e : ∏ _v ∈ sel, M₂ ^ (-(1 / 18 : ℝ)) = M₂ ^ (-((sel.card : ℝ) / 18)) := by
    rw [Finset.prod_const, ← Real.rpow_mul_natCast hM0.le]; congr 1; ring
  beta_reduce at h
  rwa [e] at h

end WaveTurbulence.Flower.SelRes
