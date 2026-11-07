/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTCond
public import WaveTurbulence.Foundations.Spine.Final4a
/-! # FLOWER-P5: `LadderFourierAtST'` from the analytic inequalities on the parameters

Copy-and-thread of `ladder_fourier_param` (`Final4a`). The time-box length bound is `P.D + 1` instead of `P.D`:
a parent of a stub has its box start at the stub time, which is at most `layer + 1`. If a floor exceeds
`layer + 1`, the domain is empty and the box sum vanishes. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint MeasureTheory Set Finset
open scoped Classical ENNReal

/-- The analytic inequalities (as `LFHyps`, with `P.D + 1` in the exponential estimate). -/
structure LFHypsST (P : WTParams) : Prop where
  d1 : 1 ≤ P.d
  Lpos : 0 < P.L
  δpos : 0 < P.δ
  δle : P.δ ≤ 1
  νnn : 0 ≤ P.ν
  Λ1 : 1 ≤ Real.log P.L
  big : Real.log P.L ^ 2 < 1 + P.δ * P.L ^ (2 * P.γ)
  Y : 3 * (2 * (2 * Real.arsinh (Mv P.d P.L) + 1)) ≤ 180 * P.d * Real.log P.L
  expb : Real.exp (((P.D : ℝ) + 1) * P.δ ^ (1 + 10 * P.ν) * Real.log P.L) * (Real.log P.L) ^ (2 * P.d + 4) ≤
    P.L ^ (P.δ ^ (5 * P.ν))
  ΛLam : (Real.log P.L) ^ 2 ≤ P.L ^ (P.δ ^ (5 * P.ν))
  free : 128 * (180 * P.d * Real.log P.L) ≤ P.L ^ (P.δ ^ (5 * P.ν))
  C : 128 * (180 * P.d) * (64 * (1 + P.d * (2 : ℝ) ^ (P.d - 1))) ≤ P.C₁
  C1 : 1 ≤ P.C₁

variable {w d : ℕ} {G : Garden w}

/-- If a floor lies above its box, the free-clock Fourier transform vanishes. -/
theorem splicedFourierBST_eq_zero (D : SplicedKernelDataST G d)
    (hne : ∃ v : FrB G D.fix, floorB D v.1 ∧ (D.layer v.1 : ℝ) + 1 < D.stubTime) (α : GBranch G.tree → ℝ) :
    splicedFourierBST G D.layer D.rootTime D.fix α = 0 := by
  unfold splicedFourierBST
  obtain ⟨v, ⟨c, hc, hch⟩, hlt⟩ := hne
  have : ∀ τ : FrB G D.fix → ℝ, (splicedTimeDomainFix G D.layer D.rootTime D.fix).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
      (G.extendFix D.fix τ) = 0 := by
    intro τ
    refine Set.indicator_of_notMem (fun hm => ?_) _
    have h1 := (hm.1 v.1 v.2).1.2
    have h2 := hm.2 c v.1 hch (Or.inr v.2)
    rw [extendFix_stub D τ c hc, extendFix_free D.fix τ v.1 v.2] at h2
    rw [extendFix_free D.fix τ v.1 v.2] at h1
    linarith
  rw [integral_congr_ae (Filter.Eventually.of_forall this), integral_zero]

theorem boxSumSTFree_eq_zero (D : SplicedKernelDataST G d)
    (hne : ∃ v : FrB G D.fix, floorB D v.1 ∧ (D.layer v.1 : ℝ) + 1 < D.stubTime)
    (A : Set (GBranch G.tree → ℝ)) :
    splicedFourierBoxSumSTFree G D.layer D.rootTime D.fix A = 0 := by
  unfold splicedFourierBoxSumSTFree
  simp only [splicedFourierBST_eq_zero D hne, enorm_zero, iSup_const]
  simp

theorem ladder_fourier_paramST (P : WTParams) (h : LFHypsST P) : LadderFourierAtST' P := by
  intro p hp R hR1 hR10 G hplain hirr hbal hord1 hord2 D scales hlayer hamp hstub base roots
  by_cases hs : ∀ v : FrB G D.fix, floorB D v.1 → D.stubTime ≤ (D.layer v.1 : ℝ) + 1
  swap
  · push_neg at hs
    obtain ⟨v, hv, hlt⟩ := hs
    rw [boxSumSTFree_eq_zero D ⟨v, hv, hlt⟩]
    exact zero_le
  have hpend := hstub.2.1
  set Dt : ℝ := (P.D : ℝ) + 1 with hDtdef
  have hDt0 : 0 ≤ Dt := by positivity
  have hDt : ∀ v, (D.layer v : ℝ) + 2 ≤ Dt := fun v => by
    have : D.layer v + 2 ≤ P.D + 1 := by have := hlayer v; omega
    rw [hDtdef]; exact_mod_cast this
  set Tr : ℝ := P.C₁ * ((P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      (P.L ^ (P.δ ^ (5 * P.ν))) ^ G.molecule.rho *
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S)
    with hTr
  have hT : Tr = P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S := by
    rw [hTr, ← Real.rpow_natCast (P.L ^ (P.δ ^ (5 * P.ν))) G.molecule.rho, ← Real.rpow_mul h.Lpos.le]
    ring
  rw [← hT]
  have hB : ∀ (π0 : PF G) (A : Finset (FrB G D.fix)),
      ∫⁻ α in Wnb (clsPFfree D scales P.L P.γ P.η P.δ base roots π0),
        ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) A α‖ₑ ≤
      ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order)) := by
    intro π0 A
    have hcard : ((Sigs G).card : ℝ≥0∞) ≠ 0 := by
      have : 0 < (Sigs G).card := Finset.card_pos.mpr ⟨π0.sig, π0.sig_mem⟩
      exact_mod_cast this.ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hcard (by positivity)))
      (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)))]
    rw [mul_comm]
    exact class_condST hplain h.Lpos D hamp hpend scales P.γ P.η P.δ h.δpos h.δle P.ν h.νnn base roots Dt
      (P.L ^ (P.δ ^ (5 * P.ν))) P.C₁ hDt0 hDt hs h.Λ1 h.big h.Y h.expb h.ΛLam h.free h.C h.C1 h.d1 π0 A
  refine (box_sum_boundST hplain h.Lpos D scales P.γ P.η P.δ base roots _ hB).trans ?_
  have hcardle : Fintype.card (FrB G D.fix) ≤ G.order := by
    rw [← card_branch_eq G]; exact Fintype.card_subtype_le _
  have h8 : (2 : ℝ≥0∞) ^ Fintype.card (FrB G D.fix) * (2 ^ Fintype.card (FrB G D.fix) *
      (2 ^ Fintype.card (FrB G D.fix) * (ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order))))) ≤
      2 ^ (3 * G.order) * (ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (3 * G.order))) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    refine mul_le_mul' (pow_le_pow_right₀ (by norm_num) (by omega)) le_rfl
  refine (mul_le_mul' le_rfl h8).trans ?_
  rw [← mul_assoc]
  exact ENNReal.mul_div_le

end WaveTurbulence.FlowerP5
