/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.CplBall

/-! # RT-GATE (ii): the couple clause per output (`rt_cpl_perk`)

At one output `k` of a lattice ball centred at `c₀`, the kernel of clause (ii) on the R189 box is bounded by
`rtCr · L² · termRb(c') · ⟨c₀⟩^{-2d}`: with one pinned root by `RtOne` (lifted from the partner clock), with both by
`RtBoth` (a constant; the two-cut part by `rt_two_le_term`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The per-output constant of clause (ii). -/
def rtCr (θ Ct₁ Ct₂ : ℝ) (d : ℕ) : ℝ :=
  ((cutNorm θ).toReal * Ct₁ + (cutNormR θ 2).toReal * Ct₂ * 2) * (tcDec d + 1) * 4 ^ d + 1

theorem rtCr_one_le {θ Ct₁ Ct₂ : ℝ} (h1 : 0 ≤ Ct₁) (h2 : 0 ≤ Ct₂) (d : ℕ) : 1 ≤ rtCr θ Ct₁ Ct₂ d := by
  unfold rtCr
  have := tcDec_nonneg d
  have : 0 ≤ ((cutNorm θ).toReal * Ct₁ + (cutNormR θ 2).toReal * Ct₂ * 2) * (tcDec d + 1) * 4 ^ d := by positivity
  linarith

theorem rt_layer_root {w : ℕ} (LG : LayeredGarden w) (j : Fin w) :
    layerAt LG (j, []) = LG.layer (GNode.root LG.garden.tree j) :=
  layerAt_of_mem LG (z := (j, [])) (TTree.nil_mem_nodes _)

theorem rt_t1sw0 : t1sw (0 : Fin 2) = 1 := rfl
theorem rt_t1sw1 : t1sw (1 : Fin 2) = 0 := rfl

/-- The box of clause (ii) with root `0` pinned: tree `0`'s clock is lowered to the pin. -/
theorem rt_box_one0 {LG : LayeredGarden 2} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Rt : Fin 2 → Prop) (h0 : Rt 0) (h1 : ¬ Rt 1) (s : ℝ)
    (ts : Fin 2 → ℝ) (hts : s ≤ ts 0) (k : Mom d) :
    kernelProt L γ δ LG H m (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 =
      kernelProt L γ δ LG H m (fun b => if b.1.1 = 0 then s else ts 1) 0 (trFix 0 s) k (fun _ => 0) 0 := by
  have hfr : ∀ b : GBranch LG.garden.tree, ¬ Rt b.1.1 →
      (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then ts 0 else ts 1) b =
        (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then s else ts 1) b := fun b hR => by
    have hb : b.1.1 ≠ 0 := fun h => hR (h ▸ h0)
    simp only [hb, if_false]
  have hu : ∀ b : GBranch LG.garden.tree, Rt b.1.1 →
      s ≤ (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then ts 0 else ts 1) b ∧
        s ≤ (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then s else ts 1) b := fun b hR => by
    have hb : b.1.1 = 0 := by
      by_contra hc
      have := rt_fin2_ne (j := 0) hc
      exact h1 (by rw [this] at hR; simpa [t1sw] using hR)
    simp only [hb, if_true]
    exact ⟨hts, le_rfl⟩
  rw [rt_kernel_up2 L γ δ H m Rt 0 s _ _ hfr hu k _ _, rt_rootPins_one Rt 0 h0 (by simpa [t1sw] using h1) s]

/-- The box of clause (ii) with root `1` pinned. -/
theorem rt_box_one1 {LG : LayeredGarden 2} (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Rt : Fin 2 → Prop) (h1 : Rt 1) (h0 : ¬ Rt 0) (s : ℝ)
    (ts : Fin 2 → ℝ) (hts : s ≤ ts 1) (k : Mom d) :
    kernelProt L γ δ LG H m (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 =
      kernelProt L γ δ LG H m (fun b => if b.1.1 = 1 then s else ts 0) 0 (trFix 1 s) k (fun _ => 0) 0 := by
  have hfr : ∀ b : GBranch LG.garden.tree, ¬ Rt b.1.1 →
      (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then ts 0 else ts 1) b =
        (fun b : GBranch LG.garden.tree => if b.1.1 = 1 then s else ts 0) b := fun b hR => by
    have hb : b.1.1 = 0 := by
      by_contra hc
      have := rt_fin2_ne (j := 0) hc
      exact hR (by rw [this]; simpa [t1sw] using h1)
    simp only [hb, if_true, show (0 : Fin 2) ≠ 1 by decide, if_false]
  have hu : ∀ b : GBranch LG.garden.tree, Rt b.1.1 →
      s ≤ (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then ts 0 else ts 1) b ∧
        s ≤ (fun b : GBranch LG.garden.tree => if b.1.1 = 1 then s else ts 0) b := fun b hR => by
    have hb : b.1.1 = 1 := by
      by_contra hc
      have := rt_fin2_ne (j := 1) hc
      exact h0 (by rw [this] at hR; simpa [t1sw] using hR)
    simp only [hb, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
    exact ⟨hts, le_rfl⟩
  rw [rt_kernel_up2 L γ δ H m Rt 0 s _ _ hfr hu k _ _, rt_rootPins_one Rt 1 h1 (by simpa [t1sw] using h0) s]

/-- Clause (ii), both roots pinned. -/
theorem rt_cpl_both {θ c' Ct₁ Ct₂ : ℝ} (hθ0 : 0 ≤ θ) (hCt₁ : 0 ≤ Ct₁) (hCt₂ : 0 ≤ Ct₂) (h1 : RtOne θ c' Ct₁)
    (h2 : RtBoth θ Ct₂) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    (hC11 : 1 ≤ P.C₁) (hθc : PieceLoss P θ c') (hδC : P.δ * P.C₁ ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hbig : termK CL (rtCr θ Ct₁ Ct₂ P.d) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (Rt : Fin 2 → Prop) (hRt : ∃ j, Rt j) (hboth : Rt 0 ∧ Rt 1 → PieceLoss P θ 0 ∧ c' = 0)
    (Q : RegCpl) (LG : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n) (hdec : Q.Decodes LG.garden)
    (hle : ∀ a, LG.layer a ≤ p)
    (hpin : ∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q') (hamb : MkSlotsO.CplAmbient p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    {b₀ c₀ k : Mom P.d} (hk : k ∈ latticeBall P.L b₀ c₀) (hb : Rt 0 ∧ Rt 1) :
    rn θ (timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links)
        (leafSizeProduct LG B) (starCost S cω)) * (jbr c₀ ^ (2 * P.d))⁻¹) := by
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  set W : ℝ := (jbr c₀ ^ (2 * P.d))⁻¹ with hW
  have hW0 : 0 ≤ W := inv_nonneg.2 (pow_nonneg (jbr_pos c₀).le _)
  set T : ℝ := (tcDec P.d + 1) * (latC P.d * P.L ^ P.d) ^ 2 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by have := tcDec_nonneg P.d; linarith) (sq_nonneg _)
  have h4 : (0 : ℝ) ≤ 4 ^ P.d := by positivity
  have hwt : tcWt P.L k ≤ ENNReal.ofReal (T * (4 ^ P.d * W)) := by
    refine (rt_tcWt_le hd1 hL1 k).trans ?_
    rw [ENNReal.ofReal_mul hT0]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (rt_ball_wt hk))
  have hcN : cutNorm θ = ENNReal.ofReal (cutNorm θ).toReal := (ENNReal.ofReal_toReal (cutNorm_lt_top θ).ne).symm
  have hcR : cutNormR θ 2 = ENNReal.ofReal (cutNormR θ 2).toReal :=
    (ENNReal.ofReal_toReal (cutNormR_lt_top θ 2).ne).symm
  have hcN0 : 0 ≤ (cutNorm θ).toReal := ENNReal.toReal_nonneg
  have hcR0 : 0 ≤ (cutNormR θ 2).toReal := ENNReal.toReal_nonneg
  have htR := termRb_nonneg (c' := c') hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have htR0 := termRb_nonneg (c' := 0) hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hRt
    exact tc_size_pos hwf hdec (hpin j hj).1 hsz
  have hLL : P.L ≤ P.L ^ (if c' = 0 then 4 else 1) := by
    split_ifs
    · calc P.L = P.L ^ 1 := (pow_one _).symm
        _ ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    · exact (pow_one _).symm.le
  have hL24 : P.L ^ 2 ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hcc : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hrb := rb_nonneg hC1 K.hδ hL0 (n - 1) (LG.incoherency Q.links)
  -- both roots pinned: a constant
  obtain ⟨hθ0', hc'0⟩ := hboth hb
  subst hc'0
  have hq0 : q = p := le_antisymm hq (by have := (hpin 0 hb.1).2; omega)
  have hq1 : q' = p := le_antisymm hq' (by have := (hpin 1 hb.2).2; omega)
  have hall : ∀ j, Rt j := fun j => by fin_cases j; exacts [hb.1, hb.2]
  set V := kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ) (fun _ => s) 0
    (MkSlotsO.rootPins (fun _ => True) s) k (fun _ => 0) 0 with hV
  have hF : ∀ ts ∈ timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j},
      kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 = V := by
    intro ts hts
    rw [rt_rootPins_both Rt hall s, hV]
    refine rt_kernel_up2 P.L P.γ P.δ H _ (fun _ => True) 0 s _ _ (fun _ h => absurd trivial h) (fun b _ => ?_) k _ _
    refine ⟨?_, le_rfl⟩
    split_ifs with h0
    · exact hts.2 0 hb.1
    · exact hts.2 1 hb.2
  rw [rn_congr θ hF]
  have hcell : timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j} ⊆ VineEstS3.FS.cell ![(q : ℝ), q'] :=
    fun ts hts i => by
      fin_cases i
      · simpa using hts.1.1
      · simpa using hts.1.2
  refine (rn_const_le θ ![(q : ℝ), q'] hcell V).trans ?_
  have hamb' : MkSlotsO.CplAmbient p p p Q LG := by subst hq0; subst hq1; exact hamb
  have hVb := h2 K hFC hC11 hθ0' hp hn Q LG hwf hsz hdec hle hamb'
    (fun j => by rw [rt_layer_root]; exact (hpin j (hall j)).2) (fun j => (hpin j (hall j)).1) hps hsp H B hH S ω
    cω hpres ∅ (fun _ => P.L) (by simp) ∅ (fun _ => P.L) (by simp) k
  rw [rt_gateM_empty] at hVb
  have h2t := rt_two_le_term (CL := CL) (Cr := rtCr θ Ct₁ Ct₂ P.d) hL1 K.hδ hC11 hδC
    (one_le_mul_of_one_le_of_one_le hCL1 (rtCr_one_le hCt₁ hCt₂ P.d)) hbig hn1 (LG.incoherency Q.links) hleaf hCS
  set Y : ℝ := P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) +
    coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
      (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (n - 2) (LG.incoherency Q.links)))) with hY
  have hY0 : 0 ≤ Y := by
    have := rb_nonneg hC1 K.hδ hL0 (n - 2) (LG.incoherency Q.links)
    have := latC_nonneg P.d
    have := pow_nonneg hL0 P.d
    positivity
  have hYT : Y * leafSizeProduct LG B * starCost S cω * T ≤
      (tcDec P.d + 1) * (P.L ^ 2 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) +
        P.L ^ 2 * twoRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) := by
    rw [hY, hT]
    unfold termRb twoRb
    simp only [Real.rpow_zero, mul_zero, one_mul, mul_one]
    apply le_of_eq
    ring
  calc ‖V‖ₑ * cutNormR θ 2
      ≤ (ENNReal.ofReal (Ct₂ * (Y * leafSizeProduct LG B * starCost S cω)) * ENNReal.ofReal (T * (4 ^ P.d * W))) *
          ENNReal.ofReal (cutNormR θ 2).toReal := by
        rw [← hcR]
        refine mul_le_mul' (hVb.trans (mul_le_mul' (le_of_eq ?_) hwt)) le_rfl
        rw [hY]
    _ = ENNReal.ofReal ((cutNormR θ 2).toReal * Ct₂ * (4 ^ P.d) *
          ((Y * leafSizeProduct LG B * starCost S cω * T)) * W) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hCt₂ (by positivity)), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ENNReal.ofReal ((cutNormR θ 2).toReal * Ct₂ * (4 ^ P.d) *
          ((tcDec P.d + 1) * (2 * (P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)))) * W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm : 0 ≤ (cutNormR θ 2).toReal * Ct₂ * (4 ^ P.d) := by positivity
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hYT.trans ?_) hm) hW0
        have := tcDec_nonneg P.d
        have hL2' : 0 ≤ P.L ^ 2 := by positivity
        have e1 : P.L ^ 2 * twoRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) ≤
            P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) := by
          calc P.L ^ 2 * twoRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)
              ≤ P.L ^ 2 * (P.L ^ 2 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) :=
                mul_le_mul_of_nonneg_left h2t hL2'
            _ = P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) := by ring
        have e2 : P.L ^ 2 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) ≤
            P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) :=
          mul_le_mul_of_nonneg_right hL24 htR0
        nlinarith
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hX : 0 ≤ P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W := by positivity
        have hcoef : (cutNormR θ 2).toReal * Ct₂ * 2 * (tcDec P.d + 1) * 4 ^ P.d ≤ rtCr θ Ct₁ Ct₂ P.d := by
          unfold rtCr
          have := tcDec_nonneg P.d
          have : 0 ≤ (cutNorm θ).toReal * Ct₁ * (tcDec P.d + 1) * 4 ^ P.d := by positivity
          nlinarith
        calc (cutNormR θ 2).toReal * Ct₂ * 4 ^ P.d * ((tcDec P.d + 1) *
              (2 * (P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)))) * W
            = ((cutNormR θ 2).toReal * Ct₂ * 2 * (tcDec P.d + 1) * 4 ^ P.d) *
                (P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) := by ring
          _ ≤ rtCr θ Ct₁ Ct₂ P.d * (P.L ^ 4 * termRb P 0 n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) :=
              mul_le_mul_of_nonneg_right hcoef hX
          _ = _ := by
              split_ifs with hc
              · ring
              · exact absurd rfl hc

/-- Clause (ii), one root pinned. -/
theorem rt_cpl_one0 {θ c' Ct₁ Ct₂ : ℝ} (hθ0 : 0 ≤ θ) (hCt₁ : 0 ≤ Ct₁) (hCt₂ : 0 ≤ Ct₂) (h1 : RtOne θ c' Ct₁)
    (h2 : RtBoth θ Ct₂) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    (hC11 : 1 ≤ P.C₁) (hθc : PieceLoss P θ c') (hδC : P.δ * P.C₁ ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hbig : termK CL (rtCr θ Ct₁ Ct₂ P.d) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (Rt : Fin 2 → Prop) (hRt : ∃ j, Rt j) (hboth : Rt 0 ∧ Rt 1 → PieceLoss P θ 0 ∧ c' = 0)
    (Q : RegCpl) (LG : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n) (hdec : Q.Decodes LG.garden)
    (hle : ∀ a, LG.layer a ≤ p)
    (hpin : ∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q') (hamb : MkSlotsO.CplAmbient p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    {b₀ c₀ k : Mom P.d} (hk : k ∈ latticeBall P.L b₀ c₀) (h0 : Rt 0) (h1' : ¬ Rt 1) :
    rn θ (timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links)
        (leafSizeProduct LG B) (starCost S cω)) * (jbr c₀ ^ (2 * P.d))⁻¹) := by
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  set W : ℝ := (jbr c₀ ^ (2 * P.d))⁻¹ with hW
  have hW0 : 0 ≤ W := inv_nonneg.2 (pow_nonneg (jbr_pos c₀).le _)
  set T : ℝ := (tcDec P.d + 1) * (latC P.d * P.L ^ P.d) ^ 2 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by have := tcDec_nonneg P.d; linarith) (sq_nonneg _)
  have h4 : (0 : ℝ) ≤ 4 ^ P.d := by positivity
  have hwt : tcWt P.L k ≤ ENNReal.ofReal (T * (4 ^ P.d * W)) := by
    refine (rt_tcWt_le hd1 hL1 k).trans ?_
    rw [ENNReal.ofReal_mul hT0]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (rt_ball_wt hk))
  have hcN : cutNorm θ = ENNReal.ofReal (cutNorm θ).toReal := (ENNReal.ofReal_toReal (cutNorm_lt_top θ).ne).symm
  have hcR : cutNormR θ 2 = ENNReal.ofReal (cutNormR θ 2).toReal :=
    (ENNReal.ofReal_toReal (cutNormR_lt_top θ 2).ne).symm
  have hcN0 : 0 ≤ (cutNorm θ).toReal := ENNReal.toReal_nonneg
  have hcR0 : 0 ≤ (cutNormR θ 2).toReal := ENNReal.toReal_nonneg
  have htR := termRb_nonneg (c' := c') hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have htR0 := termRb_nonneg (c' := 0) hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hRt
    exact tc_size_pos hwf hdec (hpin j hj).1 hsz
  have hLL : P.L ≤ P.L ^ (if c' = 0 then 4 else 1) := by
    split_ifs
    · calc P.L = P.L ^ 1 := (pow_one _).symm
        _ ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    · exact (pow_one _).symm.le
  have hL24 : P.L ^ 2 ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hcc : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hrb := rb_nonneg hC1 K.hδ hL0 (n - 1) (LG.incoherency Q.links)
  -- the common algebra
  have halg : ∀ (X : ℝ≥0∞), X ≤ ENNReal.ofReal (Ct₁ * (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B * starCost S cω)))) * tcWt P.L k →
      cutNorm θ * X ≤ ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) *
        termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) * W) := by
    intro X hX
    have hLc := Real.rpow_nonneg hL0 (4 * c')
    have hZ0 : 0 ≤ P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) *
        leafSizeProduct LG B * starCost S cω)) := by positivity
    have hZT : P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) *
        leafSizeProduct LG B * starCost S cω)) * T =
        (tcDec P.d + 1) * (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) := by
      rw [hT]; unfold termRb; ring
    calc cutNorm θ * X
        ≤ ENNReal.ofReal (cutNorm θ).toReal * (ENNReal.ofReal (Ct₁ * (P.L ^ (4 * c') * (P.L *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B *
              starCost S cω)))) * ENNReal.ofReal (T * (4 ^ P.d * W))) := by
          rw [← hcN]; exact mul_le_mul' le_rfl (hX.trans (mul_le_mul' le_rfl hwt))
      _ = ENNReal.ofReal ((cutNorm θ).toReal * Ct₁ * 4 ^ P.d * (P.L ^ (4 * c') * (P.L *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B *
              starCost S cω)) * T) * W) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hCt₁ hZ0), ← ENNReal.ofReal_mul hcN0]
          congr 1; ring
      _ ≤ _ := by
          rw [hZT]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcoef : (cutNorm θ).toReal * Ct₁ * (tcDec P.d + 1) * 4 ^ P.d ≤ rtCr θ Ct₁ Ct₂ P.d := by
            unfold rtCr
            have := tcDec_nonneg P.d
            have : 0 ≤ (cutNormR θ 2).toReal * Ct₂ * 2 * (tcDec P.d + 1) * 4 ^ P.d := by positivity
            nlinarith
          have hX1 : 0 ≤ P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W := by positivity
          calc (cutNorm θ).toReal * Ct₁ * 4 ^ P.d * ((tcDec P.d + 1) *
                (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω))) * W
              = ((cutNorm θ).toReal * Ct₁ * (tcDec P.d + 1) * 4 ^ P.d) *
                  (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) := by ring
            _ ≤ rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) := by
                refine mul_le_mul hcoef ?_ hX1 (by have := rtCr_one_le (θ := θ) hCt₁ hCt₂ P.d; linarith)
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLL htR) hW0
            _ = _ := by ring
  -- root 0 pinned, partner window `q'`
  have hqp : q = p := le_antisymm hq (by have := (hpin 0 h0).2; omega)
  obtain ⟨f, hf⟩ : ∃ f : (Fin 1 → ℝ) → ℂ, f = fun y => kernelProt P.L P.γ P.δ LG H
      (gateM S ω ∅ (fun _ => P.L) ∅ (fun _ => P.L)) (fun b => if b.1.1 = 0 then s else y 0) 0 (trFix 0 s) k
      (fun _ => 0) 0 := ⟨_, rfl⟩
  have hF : ∀ ts ∈ timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j},
      kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 =
      f (fun _ => ts 1) := by
    intro ts hts
    rw [hf, rt_gateM_empty]
    exact rt_box_one0 P.L P.γ P.δ H _ Rt h0 h1' s ts (hts.2 0 h0) k
  rw [rn_congr θ hF]
  refine (rn_lift2 hθ0 q q' Set.inter_subset_left f).trans ?_
  refine halg _ ?_
  have hamb' : MkSlotsO.CplAmbient p (rtWin p q' 0 0) (rtWin p q' 0 1) Q LG := by
    have e0 : rtWin p q' 0 0 = q := by simp [rtWin, hqp]
    have e1 : rtWin p q' 0 1 = q' := by simp [rtWin]
    rw [e0, e1]; exact hamb
  have hj0 : layerAt LG ((0 : Fin 2), []) = p := (rt_layer_root LG 0).trans (hpin 0 h0).2
  have hr' : layerAt LG (t1sw 0, []) ≤ q' := by
    rw [rt_t1sw0]; exact (rt_layer_root LG 1).trans_le hr1
  have hM : ∀ b ∈ (∅ : Finset (GBranch LG.garden.tree)), P.L ≤ (fun _ => P.L) b :=
    fun b hb => absurd hb (Finset.notMem_empty b)
  have hres := h1 K hFC hC11 hθc hp hn Q LG hwf hsz hdec hle 0 hq' hamb' hj0 (hpin 0 h0).1 hr' hps hsp H B hH
    S ω cω hpres ∅ (fun _ => P.L) hM ∅ (fun _ => P.L) hM k
  rw [hf]
  exact hres

/-- Clause (ii), one root pinned. -/
theorem rt_cpl_one1 {θ c' Ct₁ Ct₂ : ℝ} (hθ0 : 0 ≤ θ) (hCt₁ : 0 ≤ Ct₁) (hCt₂ : 0 ≤ Ct₂) (h1 : RtOne θ c' Ct₁)
    (h2 : RtBoth θ Ct₂) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    (hC11 : 1 ≤ P.C₁) (hθc : PieceLoss P θ c') (hδC : P.δ * P.C₁ ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hbig : termK CL (rtCr θ Ct₁ Ct₂ P.d) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (Rt : Fin 2 → Prop) (hRt : ∃ j, Rt j) (hboth : Rt 0 ∧ Rt 1 → PieceLoss P θ 0 ∧ c' = 0)
    (Q : RegCpl) (LG : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n) (hdec : Q.Decodes LG.garden)
    (hle : ∀ a, LG.layer a ≤ p)
    (hpin : ∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q') (hamb : MkSlotsO.CplAmbient p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    {b₀ c₀ k : Mom P.d} (hk : k ∈ latticeBall P.L b₀ c₀) (h1' : Rt 1) (h0 : ¬ Rt 0) :
    rn θ (timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links)
        (leafSizeProduct LG B) (starCost S cω)) * (jbr c₀ ^ (2 * P.d))⁻¹) := by
  have hL1 := K.hL
  have hL0 : (0 : ℝ) ≤ P.L := by linarith
  have hC1 : 0 ≤ P.C₁ := by linarith
  have hd1 : 1 ≤ P.d := by have := K.hd; omega
  have hleaf : 0 ≤ leafSizeProduct LG B := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hCS := starCost_nonneg' S cω
  set W : ℝ := (jbr c₀ ^ (2 * P.d))⁻¹ with hW
  have hW0 : 0 ≤ W := inv_nonneg.2 (pow_nonneg (jbr_pos c₀).le _)
  set T : ℝ := (tcDec P.d + 1) * (latC P.d * P.L ^ P.d) ^ 2 with hT
  have hT0 : 0 ≤ T := mul_nonneg (by have := tcDec_nonneg P.d; linarith) (sq_nonneg _)
  have h4 : (0 : ℝ) ≤ 4 ^ P.d := by positivity
  have hwt : tcWt P.L k ≤ ENNReal.ofReal (T * (4 ^ P.d * W)) := by
    refine (rt_tcWt_le hd1 hL1 k).trans ?_
    rw [ENNReal.ofReal_mul hT0]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (rt_ball_wt hk))
  have hcN : cutNorm θ = ENNReal.ofReal (cutNorm θ).toReal := (ENNReal.ofReal_toReal (cutNorm_lt_top θ).ne).symm
  have hcR : cutNormR θ 2 = ENNReal.ofReal (cutNormR θ 2).toReal :=
    (ENNReal.ofReal_toReal (cutNormR_lt_top θ 2).ne).symm
  have hcN0 : 0 ≤ (cutNorm θ).toReal := ENNReal.toReal_nonneg
  have hcR0 : 0 ≤ (cutNormR θ 2).toReal := ENNReal.toReal_nonneg
  have htR := termRb_nonneg (c' := c') hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have htR0 := termRb_nonneg (c' := 0) hC1 K.hδ hL0 n (LG.incoherency Q.links) hleaf hCS
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hRt
    exact tc_size_pos hwf hdec (hpin j hj).1 hsz
  have hLL : P.L ≤ P.L ^ (if c' = 0 then 4 else 1) := by
    split_ifs
    · calc P.L = P.L ^ 1 := (pow_one _).symm
        _ ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    · exact (pow_one _).symm.le
  have hL24 : P.L ^ 2 ≤ P.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hcc : 0 ≤ coupling P.d P.L P.γ P.δ ^ 2 := sq_nonneg _
  have hrb := rb_nonneg hC1 K.hδ hL0 (n - 1) (LG.incoherency Q.links)
  -- the common algebra
  have halg : ∀ (X : ℝ≥0∞), X ≤ ENNReal.ofReal (Ct₁ * (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B * starCost S cω)))) * tcWt P.L k →
      cutNorm θ * X ≤ ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) *
        termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) * W) := by
    intro X hX
    have hLc := Real.rpow_nonneg hL0 (4 * c')
    have hZ0 : 0 ≤ P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) *
        leafSizeProduct LG B * starCost S cω)) := by positivity
    have hZT : P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) *
        leafSizeProduct LG B * starCost S cω)) * T =
        (tcDec P.d + 1) * (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω)) := by
      rw [hT]; unfold termRb; ring
    calc cutNorm θ * X
        ≤ ENNReal.ofReal (cutNorm θ).toReal * (ENNReal.ofReal (Ct₁ * (P.L ^ (4 * c') * (P.L *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B *
              starCost S cω)))) * ENNReal.ofReal (T * (4 ^ P.d * W))) := by
          rw [← hcN]; exact mul_le_mul' le_rfl (hX.trans (mul_le_mul' le_rfl hwt))
      _ = ENNReal.ofReal ((cutNorm θ).toReal * Ct₁ * 4 ^ P.d * (P.L ^ (4 * c') * (P.L *
            (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 3 * rb P (n - 1) (LG.incoherency Q.links)) * leafSizeProduct LG B *
              starCost S cω)) * T) * W) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hCt₁ hZ0), ← ENNReal.ofReal_mul hcN0]
          congr 1; ring
      _ ≤ _ := by
          rw [hZT]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcoef : (cutNorm θ).toReal * Ct₁ * (tcDec P.d + 1) * 4 ^ P.d ≤ rtCr θ Ct₁ Ct₂ P.d := by
            unfold rtCr
            have := tcDec_nonneg P.d
            have : 0 ≤ (cutNormR θ 2).toReal * Ct₂ * 2 * (tcDec P.d + 1) * 4 ^ P.d := by positivity
            nlinarith
          have hX1 : 0 ≤ P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W := by positivity
          calc (cutNorm θ).toReal * Ct₁ * 4 ^ P.d * ((tcDec P.d + 1) *
                (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω))) * W
              = ((cutNorm θ).toReal * Ct₁ * (tcDec P.d + 1) * 4 ^ P.d) *
                  (P.L * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) := by ring
            _ ≤ rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links) (leafSizeProduct LG B) (starCost S cω) * W) := by
                refine mul_le_mul hcoef ?_ hX1 (by have := rtCr_one_le (θ := θ) hCt₁ hCt₂ P.d; linarith)
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLL htR) hW0
            _ = _ := by ring
  -- root 1 pinned, partner window `q`
  have hqp : q' = p := le_antisymm hq' (by have := (hpin 1 h1').2; omega)
  obtain ⟨f, hf⟩ : ∃ f : (Fin 1 → ℝ) → ℂ, f = fun y => kernelProt P.L P.γ P.δ LG H
      (gateM S ω ∅ (fun _ => P.L) ∅ (fun _ => P.L)) (fun b => if b.1.1 = 1 then s else y 0) 0 (trFix 1 s) k
      (fun _ => 0) 0 := ⟨_, rfl⟩
  have hF : ∀ ts ∈ timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j},
      kernelProt P.L P.γ P.δ LG H (fun κ => Flower.IncTop.starWeight S ω κ)
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0 =
      f (fun _ => ts 0) := by
    intro ts hts
    rw [hf, rt_gateM_empty]
    exact rt_box_one1 P.L P.γ P.δ H _ Rt h1' h0 s ts (hts.2 1 h1') k
  rw [rn_congr θ hF]
  refine (rt_rn_lift0 hθ0 q q' Set.inter_subset_left f).trans ?_
  refine halg _ ?_
  have hamb' : MkSlotsO.CplAmbient p (rtWin p q 1 0) (rtWin p q 1 1) Q LG := by
    have e0 : rtWin p q 1 0 = q := by simp [rtWin]
    have e1 : rtWin p q 1 1 = q' := by simp [rtWin, hqp]
    rw [e0, e1]; exact hamb
  have hj1 : layerAt LG ((1 : Fin 2), []) = p := (rt_layer_root LG 1).trans (hpin 1 h1').2
  have hr' : layerAt LG (t1sw 1, []) ≤ q := by
    rw [rt_t1sw1]; exact (rt_layer_root LG 0).trans_le hr0
  have hM : ∀ b ∈ (∅ : Finset (GBranch LG.garden.tree)), P.L ≤ (fun _ => P.L) b :=
    fun b hb => absurd hb (Finset.notMem_empty b)
  have hres := h1 K hFC hC11 hθc hp hn Q LG hwf hsz hdec hle 1 hq hamb' hj1 (hpin 1 h1').1 hr' hps hsp H B hH
    S ω cω hpres ∅ (fun _ => P.L) hM ∅ (fun _ => P.L) hM k
  rw [hf]
  exact hres


/-- **Clause (ii) at one output of a lattice ball.** -/
theorem rt_cpl_perk {θ c' Ct₁ Ct₂ : ℝ} (hθ0 : 0 ≤ θ) (hCt₁ : 0 ≤ Ct₁) (hCt₂ : 0 ≤ Ct₂) (h1 : RtOne θ c' Ct₁)
    (h2 : RtBoth θ Ct₂) {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (K : AlphaConsts P C₁a C₂a C₁b C₂b) (hFC : TcFC P)
    (hC11 : 1 ≤ P.C₁) (hθc : PieceLoss P θ c') (hδC : P.δ * P.C₁ ≤ 1) {CL : ℝ} (hCL1 : 1 ≤ CL)
    (hbig : termK CL (rtCr θ Ct₁ Ct₂ P.d) P.d * P.δ * P.C₁ ^ 2 * P.L ^ (2 * P.γ) ≤ P.L ^ (2 : ℝ))
    {p : ℕ} (hp : p < P.D) {n : ℕ} (hn : n ≤ P.N (p + 1) ^ 4) {s : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (Rt : Fin 2 → Prop) (hRt : ∃ j, Rt j) (hboth : Rt 0 ∧ Rt 1 → PieceLoss P θ 0 ∧ c' = 0)
    (Q : RegCpl) (LG : LayeredGarden 2) (hwf : Q.wf = true) (hsz : Q.size = 2 * n) (hdec : Q.Decodes LG.garden)
    (hle : ∀ a, LG.layer a ≤ p)
    (hpin : ∀ j, Rt j → ([] : TTree.Path) ∈ (LG.garden.tree j).branching ∧ LG.layer (GNode.root LG.garden.tree j) = p)
    {q q' : ℕ} (hq : q ≤ p) (hq' : q' ≤ p) (hr0 : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hr1 : LG.layer (GNode.root LG.garden.tree 1) ≤ q') (hamb : MkSlotsO.CplAmbient p q q' Q LG)
    (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ) (hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal) (hH : LeafwiseControlled LG H B)
    {b₀ c₀ k : Mom P.d} (hk : k ∈ latticeBall P.L b₀ c₀) :
    rn θ (timeBox (q : ℝ) q' ∩ {ts | ∀ j, Rt j → s ≤ ts j}) (fun ts => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
        (MkSlotsO.rootPins Rt s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (rtCr θ Ct₁ Ct₂ P.d * (P.L ^ (if c' = 0 then 4 else 1) * termRb P c' n (LG.incoherency Q.links)
        (leafSizeProduct LG B) (starCost S cω)) * (jbr c₀ ^ (2 * P.d))⁻¹) := by
  by_cases hb : Rt 0 ∧ Rt 1
  · exact rt_cpl_both hθ0 hCt₁ hCt₂ h1 h2 K hFC hC11 hθc hδC hCL1 hbig hp hn hps hsp Rt hRt hboth Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω hpres H B hH hk hb
  · rcases (show (Rt 0 ∧ ¬ Rt 1) ∨ (Rt 1 ∧ ¬ Rt 0) by
      obtain ⟨j, hj⟩ := hRt
      fin_cases j
      · exact Or.inl ⟨hj, fun h => hb ⟨hj, h⟩⟩
      · exact Or.inr ⟨hj, fun h => hb ⟨h, hj⟩⟩) with ⟨h0, h1'⟩ | ⟨h1', h0⟩
    · exact rt_cpl_one0 hθ0 hCt₁ hCt₂ h1 h2 K hFC hC11 hθc hδC hCL1 hbig hp hn hps hsp Rt hRt hboth Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω hpres H B hH hk h0 h1'
    · exact rt_cpl_one1 hθ0 hCt₁ hCt₂ h1 h2 K hFC hC11 hθc hδC hCL1 hbig hp hn hps hsp Rt hRt hboth Q LG hwf hsz hdec hle hpin hq hq' hr0 hr1 hamb S ω cω hpres H B hH hk h1' h0

end WaveTurbulence.Flower.ProtRT
