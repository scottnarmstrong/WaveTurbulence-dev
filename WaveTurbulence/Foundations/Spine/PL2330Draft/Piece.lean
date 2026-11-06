/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.PieceTree

/-!
# Prop 6.1 at `Λ₁ = 30d`, `q > q'`: the single-layer slices (PL23-30D)

* `SNorm_LeafApp_tree_le`, `SNorm_LeafApp_couple_le`: leading terms at fixed times in `𝔖^{Λ,Λ₂}`;
* `tree_middle_bounds30`: error and leading term of a middle tree factor at `(r+1, r)` in `𝔖^{30d,0}`;
* `tree_top_bounds30`: the top tree factor on a target box, in `𝔛^{η,30d,0}`;
* `tree_bottom_bounds30`, `couple_bottom_bounds30`: the bottom factors, traces at `t = r+1`.
-/

@[expose] public section

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL2330

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.NormBridgeScratch

variable {d : ℕ}

theorem contDiff_of_SNorm_lt_top {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) {f : Mom d → ℂ} (h : SNorm Λ Λ₂ f < ⊤) :
    ContDiff ℝ Λ f := by
  rw [SNorm_eq_spatialNorm] at h
  exact contDiff_of_spatialNorm_lt_top hΛ h

theorem SNorm_sum_Mz_le {ι : Type*} (S : Finset ι) (Mz : ι → Mom d → ℂ) (Jc : ℂ) {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0)
    {m cJ : ℝ} (hm : 0 ≤ m) (hcJ : 0 ≤ cJ) (hJ : ‖Jc‖ ≤ cJ)
    (hM : ∀ Z ∈ S, SNorm Λ Λ₂ (Mz Z) ≤ ENNReal.ofReal m) {n : ℕ} (hS : S.card ≤ 2 ^ n) :
    SNorm Λ Λ₂ (fun k => ∑ Z ∈ S, Mz Z k * Jc) ≤ ENNReal.ofReal (2 ^ n * (cJ * m)) := by
  have hf : ∀ Z ∈ S, ContDiff ℝ Λ (fun k => Jc * Mz Z k) := fun Z hZ =>
    (contDiff_of_SNorm_lt_top hΛ ((hM Z hZ).trans_lt ENNReal.ofReal_lt_top)).const_smul Jc
  have hb : ∀ Z ∈ S, SNorm Λ Λ₂ (fun k => Jc * Mz Z k) ≤ ENNReal.ofReal (cJ * m) := fun Z hZ =>
    (SNorm_const_mul_bound hΛ Jc (Mz Z) (hM Z hZ)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hJ hm))
  have h := WaveTurbulence.Induct.SNorm_finset_sum_bound S (fun Z k => Jc * Mz Z k) (fun _ => cJ * m) hf
    (fun _ _ => mul_nonneg hcJ hm) hb
  have e : (fun k => ∑ Z ∈ S, Mz Z k * Jc) = fun k => ∑ Z ∈ S, Jc * Mz Z k := by
    funext k; exact Finset.sum_congr rfl fun Z _ => mul_comm _ _
  rw [e]
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (S.card : ℝ) ≤ 2 ^ n := by exact_mod_cast hS
  nlinarith [mul_nonneg hcJ hm]

/-- **The leading term of a tree code at fixed times in `𝔖^{Λ,Λ₂}`.** -/
theorem SNorm_LeafApp_tree_le {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) (H : LeafProfiles 1 d) (X : RegChain)
    (ζ : ℤˣ) {n : ℕ} (hsize : X.size = 2 * n) (t s : ℝ) {cJ cM : ℝ} {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0)
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM) (hJ : X.dominant = true → |X.JBtree r t s| ≤ cJ)
    (hM : X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks ζ),
      SNormR Λ Λ₂ (LeafApp.chainNstar H Z X ζ (0, [])) ≤ ENNReal.ofReal cM) :
    SNorm Λ Λ₂ (fun k => LeafApp.tree δ r H X ζ t s k) ≤ ENNReal.ofReal (δ ^ n * 2 ^ n * cJ * cM) := by
  by_cases hdom : X.dominant = true
  · have e : (fun k => LeafApp.tree δ r H X ζ t s k) =
        fun k => ∑ Z ∈ specialSets (X.treeLinks ζ), treeMz δ H X ζ Z k * (X.JBtree r t s : ℂ) :=
      funext fun k => tree_eq_sum H X ζ hdom t s k
    rw [e]
    have h := SNorm_sum_Mz_le (specialSets (X.treeLinks ζ)) (fun Z k => treeMz δ H X ζ Z k)
      (X.JBtree r t s : ℂ) hΛ (m := δ ^ n * cM) (by positivity) hcJ
      (by simpa using hJ hdom) (fun Z hZ => SNorm_treeMz_le hδ H X ζ hsize hΛ hcM Z hZ (hM hdom Z hZ))
      (card_specialSets_tree_le hsize ζ)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hcJ hcM]
  · have e : (fun k => LeafApp.tree δ r H X ζ t s k) = fun _ => 0 :=
      funext fun k => tree_eq_zero H X ζ hdom t s k
    rw [e, SNorm_eq_spatialNorm, spatialNorm_zero_fun]
    exact zero_le

/-- **The leading term of a couple code at fixed times in `𝔖^{Λ,Λ₂}`.** -/
theorem SNorm_LeafApp_couple_le {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) (H : LeafProfiles 2 d) (Q : RegCpl)
    {n : ℕ} (hsize : Q.size = 2 * n) (t s : ℝ) {cJ cM : ℝ} {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0)
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM) (hJ : Q.dominant = true → |Q.JB r t s| ≤ cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR Λ Λ₂ (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM) :
    SNorm Λ Λ₂ (fun k => LeafApp.couple δ r H Q t s k) ≤ ENNReal.ofReal (δ ^ n * 2 ^ n * cJ * cM) := by
  by_cases hdom : Q.dominant = true
  · have e : (fun k => LeafApp.couple δ r H Q t s k) =
        fun k => ∑ Z ∈ specialSets Q.links, coupleMz δ H Q Z k * (Q.JB r t s : ℂ) :=
      funext fun k => couple_eq_sum H Q hdom t s k
    rw [e]
    have h := SNorm_sum_Mz_le (specialSets Q.links) (fun Z k => coupleMz δ H Q Z k)
      (Q.JB r t s : ℂ) hΛ (m := δ ^ n * cM) (by positivity) hcJ
      (by simpa using hJ hdom) (fun Z hZ => SNorm_coupleMz_le hδ H Q hsize hΛ hcM Z (hM hdom Z hZ))
      (card_specialSets_couple_le hsize)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_nonneg hcJ hcM]
  · have e : (fun k => LeafApp.couple δ r H Q t s k) = fun _ => 0 :=
      funext fun k => couple_eq_zero H Q hdom t s k
    rw [e, SNorm_eq_spatialNorm, spatialNorm_zero_fun]
    exact zero_le

end WaveTurbulence.PL2330
