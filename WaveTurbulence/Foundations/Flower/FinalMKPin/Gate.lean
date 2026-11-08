/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.ClassCond
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the gates `WTPrefix LadderFourierAtMKFace` and `WTPrefix LadderFourierAtMK`

o73 Prop 18.1 (pins and endpoint substitutions):
- `ladder_fourier_paramMK`: from the analytic inequalities `LFHypsMK` (Port's `LFHypsST` with the constant `256`).
  It is main's `ladder_fourier_param`, applied to the box sum with `E₀ ⊆ E` (`boxSumGen_mono`). The extra
  `(Lam Λ²)^{|E₀|} ≤ L^{3|E₀|}` is absorbed by `((N+1)L)^{4|E|}`.
- `ladderFourierMKFace_prefix` and `ladderFourierMK_prefix`: the parameter choices of Port's `ladderFourierST_prefix`,
  with `C₁ = 2·C1star d`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open MeasureTheory Set Finset Filter Topology
open scoped Classical ENNReal

/-- The analytic inequalities on the parameters (Port's `LFHypsST`, with `256` in place of `128`). -/
structure LFHypsMK (P : WTParams) : Prop where
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
  free : 256 * (180 * P.d * Real.log P.L) ≤ P.L ^ (P.δ ^ (5 * P.ν))
  C : 256 * (180 * P.d) * (64 * (1 + P.d * (2 : ℝ) ^ (P.d - 1))) ≤ P.C₁
  C1 : 1 ≤ P.C₁

/-- The extra cost of the exceptional set, against `((N+1)L)^{4|E|}`. -/
theorem trMK_le {w : ℕ} (G : Garden w) (scales : Finset (GBranch G.tree) → ℝ) {L γ δ ν C1 : ℝ} {e0 e : ℕ}
    (hLpos : 0 < L) (hΛ : 1 ≤ Real.log L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hC1 : 1 ≤ C1) (he : e0 ≤ e)
    (hw : 0 ≤ ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) :
    TrMK G scales L γ δ ν (L ^ (δ ^ (5 * ν))) C1 e0 ≤
      (((G.order : ℝ) + 1) * L) ^ (4 * e) *
        (C1 * (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho) *
          ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) := by
  have hL1 : 2 ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hs1 : δ ^ (5 * ν) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hLam : L ^ (δ ^ (5 * ν)) ≤ L := by
    calc L ^ (δ ^ (5 * ν)) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hs1
      _ = L := Real.rpow_one L
  have hLam1 : 1 ≤ L ^ (δ ^ (5 * ν)) := Real.one_le_rpow (by linarith) (by positivity)
  have hlog : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < L); linarith
  have hNL : L ≤ ((G.order : ℝ) + 1) * L := le_mul_of_one_le_left hL0 (by have : (0:ℝ) ≤ G.order := Nat.cast_nonneg _; linarith)
  have hq : L ^ (δ ^ (5 * ν)) * Real.log L ^ 2 ≤ (((G.order : ℝ) + 1) * L) ^ 4 := by
    have hl0 : 0 ≤ Real.log L := by linarith
    calc L ^ (δ ^ (5 * ν)) * Real.log L ^ 2 ≤ L * L ^ 2 :=
          mul_le_mul hLam (pow_le_pow_left₀ hl0 hlog 2) (by positivity) hL0
      _ = L ^ 3 := by ring
      _ ≤ L ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ _ := pow_le_pow_left₀ hL0 hNL 4
  have hq1 : 1 ≤ L ^ (δ ^ (5 * ν)) * Real.log L ^ 2 := by nlinarith
  have hpow : (L ^ (δ ^ (5 * ν)) * Real.log L ^ 2) ^ e0 ≤ (((G.order : ℝ) + 1) * L) ^ (4 * e) := by
    calc (L ^ (δ ^ (5 * ν)) * Real.log L ^ 2) ^ e0 ≤ ((((G.order : ℝ) + 1) * L) ^ 4) ^ e0 := by gcongr
      _ = (((G.order : ℝ) + 1) * L) ^ (4 * e0) := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hrho : (L ^ (δ ^ (5 * ν))) ^ G.molecule.rho = L ^ (δ ^ (5 * ν) * G.molecule.rho) := by
    rw [← Real.rpow_natCast (L ^ (δ ^ (5 * ν))) G.molecule.rho, ← Real.rpow_mul hL0]
  have hDl1 := one_le_Dl hδ hδ1 hν
  have hC0 : 0 ≤ C1 := by linarith
  unfold TrMK
  rw [hrho]
  have hX : 0 ≤ C1 * (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    have : 0 ≤ L ^ (δ ^ (5 * ν) * G.molecule.rho) := Real.rpow_nonneg hL0 _
    positivity
  calc C1 * ((C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho) *
        (∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) *
        (L ^ (δ ^ (5 * ν)) * Real.log L ^ 2) ^ e0)
      = (L ^ (δ ^ (5 * ν)) * Real.log L ^ 2) ^ e0 *
          (C1 * (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho) *
            ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow hX

/-- **o73 Prop 18.1 at fixed parameters.** -/
theorem ladder_fourier_paramMK (P : WTParams) (h : LFHypsMK P) : LadderFourierAtMKFace P := by
  intro p hp R hR1 hR10 G hplain hirr hbal hord1 hord2 D fix face E scales hlayer hamp hfixE hfixL hface huniq
    base roots β
  have hF : FaceOK fix face := ⟨fun v u hvu => (hface v u hvu).2.2, huniq⟩
  have hE0 : E0 fix face ⊆ E := by
    intro b hb
    simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    by_cases hfb : fix b = none
    · have hgb : face b ≠ none := fun h => hb ⟨hfb, h⟩
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hgb
      exact (hface b u hu).1
    · exact hfixE b (Option.ne_none_iff_isSome.mp hfb)
  by_cases hspec : (splicedFrequencySpectrum G D scales P.L P.γ P.η P.δ base roots).Nonempty
  swap
  · have : sourceFrequencyBoxesE G E {α | α ∈ splicedFrequencySpectrum G D scales P.L P.γ P.η P.δ base roots ∧
        ∀ v ∈ E, α v = β v} = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hspec
      ext σ; simp [sourceFrequencyBoxesE, hspec]
    unfold splicedFourierBoxSumMKFace
    rw [this]
    simp
  have hP0 : ∀ S ∈ G.molecule.maximalLadders, 0 ≤ scales S := by
    obtain ⟨α, hα⟩ := hspec
    obtain ⟨π, hπ⟩ := Set.mem_iUnion.mp (spectrum_subset_iUnion G D scales P.L P.γ P.η P.δ base roots hα)
    exact fun S hS => scale_nonneg h.Lpos.le hπ ⟨S, hS⟩
  set Dt : ℝ := (P.D : ℝ) + 1 with hDtdef
  have hDt0 : 0 ≤ Dt := by positivity
  have hDt : ∀ v, (D.layer v : ℝ) + 2 ≤ Dt := fun v => by
    have : D.layer v + 2 ≤ P.D + 1 := by have := hlayer v; omega
    rw [hDtdef]; exact_mod_cast this
  set Tr := TrMK G scales P.L P.γ P.δ P.ν (P.L ^ (P.δ ^ (5 * P.ν))) P.C₁ (E0 fix face).card with hTr
  set n := Fintype.card (Iv fix face)
  have hB : ∀ (π0 : PF G) (A : Finset (Iv fix face)),
      ∫⁻ α in Wnb (clsI D scales P.L P.γ P.η P.δ base roots π0 fix face β),
        ‖Phi (Om0 (chF fix face) (lsF D.layer fix face) (capF D.layer D.rootTime fix face))
          (lsF D.layer fix face) A α‖ₑ ≤
      ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (4 * n)) := by
    intro π0 A
    have hcard : ((Sigs G).card : ℝ≥0∞) ≠ 0 := by
      have : 0 < (Sigs G).card := Finset.card_pos.mpr ⟨π0.sig, π0.sig_mem⟩
      exact_mod_cast this.ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hcard (by positivity)))
      (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)))]
    rw [mul_comm]
    exact class_condI hplain h.Lpos D hamp scales P.γ P.η P.δ h.δpos h.δle P.ν h.νnn base roots hF β Dt
      (P.L ^ (P.δ ^ (5 * P.ν))) P.C₁ hDt0 hDt h.Λ1 h.big h.Y h.expb h.ΛLam h.free h.C h.C1 h.d1 π0 A
  rw [boxSumMKFace_eq_gen]
  refine (boxSumGen_mono hE0 β _ _).trans ?_
  rw [← boxSumMKFace_eq_gen]
  refine (box_sum_boundI hF D.layer D.rootTime D scales P.L P.γ P.η P.δ base roots β _ hB).trans ?_
  have h8 : (2 : ℝ≥0∞) ^ n * (2 ^ n * (2 ^ n * (2 ^ n * (ENNReal.ofReal Tr /
      (((Sigs G).card : ℝ≥0∞) * 2 ^ (4 * n)))))) =
      2 ^ (4 * n) * (ENNReal.ofReal Tr / (((Sigs G).card : ℝ≥0∞) * 2 ^ (4 * n))) := by
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, ← pow_add]
    congr 2; ring
  rw [h8, ← mul_assoc]
  refine ENNReal.mul_div_le.trans (ENNReal.ofReal_le_ofReal ?_)
  have hδ0 := h.δpos
  have hc : 0 ≤ P.δ * P.L ^ (2 * P.γ) := mul_nonneg hδ0.le (Real.rpow_nonneg h.Lpos.le _)
  have hw : 0 ≤ ∏ S ∈ G.molecule.maximalLadders,
      Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S := by
    apply Finset.prod_nonneg
    intro S hS
    apply pow_nonneg
    unfold Molecule.ladderWeight
    refine le_min (sq_nonneg _) ?_
    have := mul_nonneg hc (hP0 S hS); linarith
  exact trMK_le G scales h.Lpos h.Λ1 hδ0 h.δle h.νnn h.C1 (Finset.card_le_card hE0) hw

end WaveTurbulence.Flower.FinalMKPin
