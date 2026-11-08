/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.RegSum
public import WaveTurbulence.Foundations.Flower.ProtWhole.Statement
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceAlgebra

/-! # D6b: the real per-garden bound of a wholly regular component

`norm_compValue_garden`: for a width-2 garden of the carrier of `RegularComponentBoundAtI` (cap `J = {c}`),

`‖compValue …‖ ≤ gain · (fc^{3n+1} L^{31d+6} C₁ (C₁δ)^{n/2} b^n) · (L^{-(γ₁-√η)})^{gcode LG}`,

`gain = ∏_j [kSel j] R_j⁻¹ R_j^{-1/18}`, `gcode LG` the incoherency of its (unique) regular code. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtGeo
open WaveTurbulence.Flower.MkDefs

/-- The incoherency index of the (unique) regular code of a width-2 garden. -/
def gcode (LG : LayeredGarden 2) : ℕ :=
  if h : IsRegularCouple LG.garden then
    LG.incoherency (Classical.choose (existsUnique_regCpl_decodes _ h).exists).links
  else 0

theorem gcode_eq {LG : LayeredGarden 2} (h : IsRegularCouple LG.garden) {Q : RegCpl} (hwf : Q.wf = true)
    (hQ : Q.Decodes LG.garden) : gcode LG = LG.incoherency Q.links := by
  unfold gcode
  rw [dif_pos h]
  have hs := Classical.choose_spec (existsUnique_regCpl_decodes _ h).exists
  rw [(existsUnique_regCpl_decodes _ h).unique hs ⟨hwf, hQ⟩]

/-- A component value with a vanishing weight vanishes. -/
theorem compValue_wt_zero (P : WTParams) {LG : LayeredGarden 2} (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (wt : (GNode LG.garden.tree → Mom P.d) → ℝ) (hw : ∀ k, wt k = 0)
    (t : ℝ) (roots : Fin 2 → (Fin P.d → ℤ)) : compValue P (R := 1) LG fix off wt t roots = 0 := by
  unfold compValue kernelKgen
  simp [hw]

/-- The selection gain of the target. -/
def regGain (Rs : Fin 2 → ℝ) (kSel : Fin 2 → Option ℕ) : ℝ :=
  ∏ j : Fin 2, (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1)

theorem regGain_nonneg (Rs : Fin 2 → ℝ) (hRs : ∀ j, 0 ≤ Rs j) (kSel : Fin 2 → Option ℕ) : 0 ≤ regGain Rs kSel := by
  unfold regGain
  refine Finset.prod_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg (inv_nonneg.2 (hRs j)) (Real.rpow_nonneg (hRs j) _)
  · exact zero_le_one

theorem inv_sq_le_gain {R : ℝ} (hR : 1 ≤ R) : R⁻¹ * R⁻¹ ≤ R⁻¹ * R ^ (-(1 / 18 : ℝ)) := by
  have h0 : 0 < R := by linarith
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h0.le)
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hR (by norm_num)

/-- **The real per-garden bound.** -/
theorem norm_compValue_garden (P : WTParams) (hptw : ProtPtw.ProtPtwAt P) (hpin : ProtBoundAt P) (hL : 2 ≤ P.L)
    (hη : 0 ≤ P.η) (hC1 : 1 ≤ P.C₁) (hδ0 : 0 < P.δ) {p n : ℕ} (hp : p < P.D) (hn1 : 1 ≤ n)
    (hn : n ≤ P.N (p + 1) ^ 4) {t s : ℝ} (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t) {c : Fin 2}
    (pat : Fin 2 → FixPat) (kSel : Fin 2 → Option ℕ) (LG : LayeredGarden 2) (hcar : MkCarries P p n LG)
    (hcap : LG.garden.tree c = .leaf) (hG : CapGeo LG {c} p) (hpat : CapPatValid LG {c} pat p)
    (hreg : IsRegularCouple LG.garden) (hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (h : ℕ → Fin 2 → Fin 2 → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin 2 → Option ℝ) (σ : Fin 2 → Option ℕ) (Rs : Fin 2 → ℝ) (dag : Option (Fin 2 → Fin 3 → Mom P.d))
    (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r) (hRs : ∀ j, P.L ≤ Rs j) (roots : Fin 2 → (Fin P.d → ℤ)) :
    ‖compValue P (R := 1) LG (fixCap LG {c} pat t s) (offCap LG {c} dag.isSome)
        (fun k => selOK LG {c} kSel * markedWeight LG {c} p P.L Rf σ (selCap LG {c} kSel) Rs h dag k) t roots‖ ≤
      regGain Rs kSel * (Stage1W.frontierConst P.d ^ (3 * n + 1) * P.L ^ (31 * P.d + 6) *
        (P.C₁ * (P.C₁ * P.δ) ^ (n / 2)) * b ^ n) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ gcode LG := by
  have hL1 : (1 : ℝ) ≤ P.L := by linarith
  have hRs1 : ∀ j, 1 ≤ Rs j := fun j => hL1.trans (hRs j)
  have hfc : 1 ≤ Stage1W.frontierConst P.d := Stage1W.one_le_frontierConst P.d
  have hρ : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η)) := Real.rpow_nonneg (by linarith) _
  have hRHS : 0 ≤ regGain Rs kSel * (Stage1W.frontierConst P.d ^ (3 * n + 1) * P.L ^ (31 * P.d + 6) *
      (P.C₁ * (P.C₁ * P.δ) ^ (n / 2)) * b ^ n) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ gcode LG := by
    refine mul_nonneg (mul_nonneg (regGain_nonneg Rs (fun j => by linarith [hRs1 j]) kSel) ?_) (pow_nonneg hρ _)
    have : 0 ≤ P.C₁ * P.δ := by positivity
    positivity
  have hok01 : selOK LG {c} kSel = 0 ∨ selOK LG {c} kSel = 1 := by
    unfold selOK; split_ifs <;> simp
  rcases hok01 with hok | hok
  · rw [compValue_wt_zero P _ _ _ (fun k => by rw [hok, zero_mul]) t roots, norm_zero]
    exact hRHS
  have hall : ∀ j, (kSel j).isSome → (selCap LG {c} kSel j).isSome := by
    unfold selOK at hok
    split_ifs at hok with hh
    · exact hh
    · exact absurd hok (by norm_num)
  have hord : 1 ≤ LG.garden.order := by rw [hcar.2.2.1]; exact hn1
  obtain ⟨j0, X, ζ, hne, hC, hsig, hpl, Q, hwf, hQ, hlinks, hsizeQ⟩ := exists_capChain hcap hreg hord
  have D : CapG LG j0 c X ζ := capG_of_capChain hne hcap hC hsig hpl
  have hS := hC.stem
  have hXn : X.size = n := by rw [← hsizeQ, ← size_eq_order hQ, hcar.2.2.1]
  have hsize : X.size = 2 * (n / 2) := by
    have he := size_even_chain X
    rw [hXn] at he ⊢
    exact (Nat.two_mul_div_two_of_even he).symm
  obtain ⟨C, hCn, hval⟩ := D.compValue_capG P hG hS pat t s kSel Rf σ Rs h dag roots
  rw [hval]
  have hg : protIncoh X D.T1 = gcode LG := by rw [D.protIncoh_eq hQ hlinks, gcode_eq hreg hwf hQ]
  -- the selection factors
  have hkc : (kSel c).isSome = false := by
    cases hk : kSel c with
    | none => rfl
    | some k =>
      have := hall c (by rw [hk]; rfl)
      rw [D.selCap_c] at this
      exact absurd this (by simp)
  have hsel_iff : (selCap LG {c} kSel j0).isSome = (kSel j0).isSome := by
    cases hk : kSel j0 with
    | none => unfold selCap; rw [hk]; rfl
    | some k => exact hall j0 (by rw [hk]; rfl)
  set gs : ℝ := if (selCap LG {c} kSel j0).isSome then (Rs j0)⁻¹ else 1 with hgs
  have hgain : regSelConst LG c j0 Rs kSel * gs ≤ regGain Rs kSel := by
    unfold regGain regSelConst
    rw [fin2_prod _ j0 c D.ne, hkc, hgs, hsel_iff]
    simp only [Bool.false_eq_true, if_false, mul_one]
    split_ifs
    · exact inv_sq_le_gain (hRs1 j0)
    · norm_num
  have hsc0 : 0 ≤ regSelConst LG c j0 Rs kSel := by
    unfold regSelConst; split_ifs
    · exact inv_nonneg.2 (by linarith [hRs1 j0])
    · exact zero_le_one
  have hgs0 : 0 ≤ gs := by
    rw [hgs]; split_ifs
    · exact inv_nonneg.2 (by linarith [hRs1 j0])
    · exact zero_le_one
  -- the kernel, in real form
  set bN : NNReal := ⟨b, by linarith⟩
  set K := kernelProt P.L P.γ P.δ D.T1 (regH1 LG j0 h) (D.mult p P.L Rf σ Rs kSel dag) (fun _ => t) 0
    ((objCfg LG {c} pat X (j0, [])).fix X s t t) (latticePoint P.L (roots j0)) (fun _ => 0) 0 with hK
  have hfc0 : 0 ≤ Stage1W.frontierConst P.d := by linarith
  have hCδ : 0 ≤ P.C₁ * P.δ := by positivity
  have hC0 : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ (n / 2) := by positivity
  have hLκ : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (gcode LG : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hKb : ‖K‖ ≤ Stage1W.frontierConst P.d ^ (D.frontS p).card * (P.L ^ (31 * P.d + 6) * gs) *
      (P.C₁ * (P.C₁ * P.δ) ^ (n / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (gcode LG : ℝ))) *
      b ^ (inputLeaves D.T1.garden).card := by
    have hkb := D.kernel_bound P hptw hpin hL1 hη hp (le_trans (Nat.div_le_self n 2) hn) hsize hG hS hpat
      hcar.1 hs.1 hs.2 ht.2 hplain h bN hb Rf σ Rs dag (fun r hr => by linarith [hRf j0 r hr]) (hRs j0)
      (latticePoint P.L (roots j0))
    rw [Finset.prod_const, ← ENNReal.ofReal_pow hfc0, regBound, hg] at hkb
    have hleaf : leafSizeProduct D.T1 (fun _ => bN) = b ^ (inputLeaves D.T1.garden).card := by
      unfold leafSizeProduct; rw [Finset.prod_const]; rfl
    rw [hleaf, ← ENNReal.ofReal_mul (pow_nonneg hfc0 _),
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hfc0 _) (mul_nonneg (pow_nonneg (by linarith) _) hgs0)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (pow_nonneg hfc0 _)
        (mul_nonneg (pow_nonneg (by linarith) _) hgs0)) (mul_nonneg hC0 hLκ))] at hkb
    exact norm_le_of_enorm_le (by positivity) hkb
  have hfcard : Stage1W.frontierConst P.d ^ (D.frontS p).card ≤ Stage1W.frontierConst P.d ^ (3 * n + 1) := by
    refine pow_le_pow_right₀ hfc ?_
    have := D.card_frontS_le' p
    rw [hcar.2.2.1] at this
    exact this
  have hbcard : b ^ (inputLeaves D.T1.garden).card ≤ b ^ n := by
    refine pow_le_pow_right₀ hb1 ?_
    have := D.card_inputLeaves_le
    rw [hcar.2.2.1] at this
    exact this
  have hρg : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (gcode LG : ℝ)) =
      (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ gcode LG := Real.rpow_mul_natCast (by linarith) _ _
  have hite : ‖(if roots c = roots j0 then K else 0)‖ ≤ ‖K‖ := by
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  calc ‖C * (regSelConst LG c j0 Rs kSel : ℂ) * (if roots c = roots j0 then K else 0)‖
      ≤ 1 * regSelConst LG c j0 Rs kSel * ‖K‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsc0]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hCn hsc0) hite (norm_nonneg _) (by positivity)
    _ ≤ 1 * regSelConst LG c j0 Rs kSel * (Stage1W.frontierConst P.d ^ (3 * n + 1) * (P.L ^ (31 * P.d + 6) * gs) *
          (P.C₁ * (P.C₁ * P.δ) ^ (n / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (gcode LG : ℝ))) * b ^ n) := by
        refine mul_le_mul_of_nonneg_left (hKb.trans ?_) (by positivity)
        gcongr
    _ = (regSelConst LG c j0 Rs kSel * gs) * (Stage1W.frontierConst P.d ^ (3 * n + 1) * P.L ^ (31 * P.d + 6) *
          (P.C₁ * (P.C₁ * P.δ) ^ (n / 2)) * b ^ n) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ gcode LG := by
        rw [← hρg]; ring
    _ ≤ regGain Rs kSel * (Stage1W.frontierConst P.d ^ (3 * n + 1) * P.L ^ (31 * P.d + 6) *
          (P.C₁ * (P.C₁ * P.δ) ^ (n / 2)) * b ^ n) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ gcode LG := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgain ?_) (pow_nonneg hρ _)
        positivity

end WaveTurbulence.Flower.ProtWhole
