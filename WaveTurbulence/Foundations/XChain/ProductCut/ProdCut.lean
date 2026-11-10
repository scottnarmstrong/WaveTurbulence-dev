/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Chi0
public import WaveTurbulence.Frozen.Defs.ProdDyadicCut

/-!
# Product-form dyadic cutoff lemmas

`prodDyadicCut L j s y` is `Ψ_j` of DH21 L2731 for the entries `y_a`, `a ∈ s`:
`Ψ_0 = ∏ χ₀(y_a/L)`, `Ψ_j = ∏ χ₀(y_a/(2^j L)) - ∏ χ₀(y_a/(2^{j-1} L))`.
Properties used by the flower consumers: `0 ≤ Ψ_j ≤ 1`, `∑_j Ψ_j = 1`, upper support, lower support (`j ≥ 1`).
-/

@[expose] public section

open Finset

namespace WaveTurbulence

namespace XChain.ProductCut

section Chi

theorem chi0_nonneg (x : ℝ) : 0 ≤ chi0 x := Real.smoothTransition.nonneg _

theorem chi0_le_one (x : ℝ) : chi0 x ≤ 1 := Real.smoothTransition.le_one _

theorem chi0_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : chi0 y ≤ chi0 x := by
  unfold chi0
  apply Real.smoothTransition.monotone
  rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]
  linarith

theorem chi0_eq_one {x : ℝ} (h : |x| ≤ 1 / 2) : chi0 x = 1 := by
  unfold chi0
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem chi0_eq_zero {x : ℝ} (h : 1 ≤ |x|) : chi0 x = 0 := by
  unfold chi0
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

end Chi

/-- `Φ_R(y) = ∏_{a ∈ s} χ₀(y_a / R)`. -/
noncomputable def prodChi {ι : Type*} (s : Finset ι) (y : ι → ℝ) (R : ℝ) : ℝ :=
  ∏ a ∈ s, chi0 (y a / R)

theorem prodDyadicCut_def {ι : Type*} (L : ℝ) (j : ℕ) (s : Finset ι) (y : ι → ℝ) :
    prodDyadicCut L j s y =
      if j = 0 then prodChi s y L else prodChi s y (2 ^ j * L) - prodChi s y (2 ^ (j - 1) * L) := rfl

section ProdCut

variable {ι : Type*} {L : ℝ} (s : Finset ι) {y : ι → ℝ}

theorem prodChi_nonneg (R : ℝ) : 0 ≤ prodChi s y R :=
  Finset.prod_nonneg fun _ _ => chi0_nonneg _

theorem prodChi_le_one (R : ℝ) : prodChi s y R ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => chi0_nonneg _) fun _ _ => chi0_le_one _

theorem prodChi_mono (hy : ∀ a ∈ s, 0 ≤ y a) {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') :
    prodChi s y R ≤ prodChi s y R' := by
  unfold prodChi
  apply Finset.prod_le_prod₀ (fun _ _ => chi0_nonneg _)
  intro a ha
  apply chi0_anti (div_nonneg (hy a ha) (hR.le.trans hRR))
  exact div_le_div_of_nonneg_left (hy a ha) hR hRR

theorem two_pow_pred_le (hL : 0 < L) (j : ℕ) : (2 : ℝ) ^ (j - 1) * L ≤ 2 ^ j * L :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)) hL.le

theorem prodDyadicCut_nonneg (hL : 0 < L) (hy : ∀ a ∈ s, 0 ≤ y a) (j : ℕ) : 0 ≤ prodDyadicCut L j s y := by
  rw [prodDyadicCut_def]
  split_ifs with hj
  · exact prodChi_nonneg s L
  · rw [sub_nonneg]
    exact prodChi_mono s hy (by positivity) (two_pow_pred_le hL j)

theorem sum_prodDyadicCut (J : ℕ) : ∑ j ∈ range (J + 1), prodDyadicCut L j s y = prodChi s y (2 ^ J * L) := by
  induction J with
  | zero => simp [prodDyadicCut_def]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, prodDyadicCut_def, ite_eq_right_iff.2 fun h => absurd h (Nat.succ_ne_zero J)]
    simp only [Nat.add_sub_cancel]
    ring

/-- The `M₁` decomposition (consumer: `hasSum_flowerKernelGen_cut1`). -/
theorem hasSum_prodDyadicCut (hL : 0 < L) (hy : ∀ a ∈ s, 0 ≤ y a) :
    HasSum (fun j => prodDyadicCut L j s y) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => prodDyadicCut_nonneg s hL hy j)]
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ a ∈ s, 2 * y a ≤ 2 ^ J * L := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (∑ a ∈ s, 2 * y a / L) (by norm_num : (1 : ℝ) < 2)
    refine ⟨J, fun a ha => ?_⟩
    have h1 : 2 * y a / L ≤ ∑ b ∈ s, 2 * y b / L :=
      Finset.single_le_sum (f := fun b => 2 * y b / L)
        (fun b hb => by have := hy b hb; positivity) ha
    have h2 : 2 * y a / L ≤ 2 ^ J := h1.trans hJ.le
    rwa [div_le_iff₀ hL] at h2
  have key : ∀ᶠ n in Filter.atTop, ∑ j ∈ range n, prodDyadicCut L j s y = 1 := by
    refine Filter.eventually_atTop.2 ⟨J + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_prodDyadicCut]
    unfold prodChi
    apply Finset.prod_eq_one
    intro a ha
    apply chi0_eq_one
    have hm : (2 : ℝ) ^ J ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 < (2 : ℝ) ^ m * L := by positivity
    rw [abs_of_nonneg (div_nonneg (hy a ha) hpos.le), div_le_iff₀ hpos]
    linarith [hJ a ha, mul_le_mul_of_nonneg_right hm hL.le]
  exact tendsto_const_nhds.congr' (key.mono fun n h => h.symm)

/-- Upper support (consumer: `flowerKernelGen_cut1_eq_zero`, X3DaggerExpansion, X3KerInv). -/
theorem lt_of_prodDyadicCut_ne_zero (hL : 0 < L) (hy : ∀ a ∈ s, 0 ≤ y a) {j : ℕ}
    (h : prodDyadicCut L j s y ≠ 0) : ∀ a ∈ s, y a < 2 ^ j * L := by
  intro a ha
  by_contra hlt
  push Not at hlt
  apply h
  have hz : ∀ R, 0 < R → R ≤ 2 ^ j * L → prodChi s y R = 0 := by
    intro R hR hRj
    unfold prodChi
    apply Finset.prod_eq_zero ha
    apply chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg (hy a ha) hR.le), le_div_iff₀ hR]
    linarith
  rw [prodDyadicCut_def]
  split_ifs with hj
  · subst hj
    exact hz L hL (by simp)
  · rw [hz _ (by positivity) le_rfl, hz _ (by positivity) (two_pow_pred_le hL j), sub_zero]

/-- Lower support, the source of the `M₁` gain: on the support of `Ψ_j`, `j ≥ 1`, some leaf has
`y_a > 2^j L / 4`. -/
theorem exists_gt_of_prodDyadicCut_ne_zero (hL : 0 < L) (hy : ∀ a ∈ s, 0 ≤ y a) {j : ℕ} (hj : 1 ≤ j)
    (h : prodDyadicCut L j s y ≠ 0) : ∃ a ∈ s, 2 ^ j * L / 4 < y a := by
  by_contra hno
  push Not at hno
  apply h
  have h2j : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : ∀ R, 2 ^ (j - 1) * L ≤ R → prodChi s y R = 1 := by
    intro R hR
    unfold prodChi
    apply Finset.prod_eq_one
    intro a ha
    apply chi0_eq_one
    have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
    rw [abs_of_nonneg (div_nonneg (hy a ha) hRpos.le), div_le_iff₀ hRpos]
    have := hno a ha
    rw [h2j] at this
    linarith
  rw [prodDyadicCut_def]
  rw [ite_eq_right_iff.2 fun h => absurd h (by omega), h1 _ (two_pow_pred_le hL j), h1 _ le_rfl, sub_self]

/-- `|Ψ_j| ≤ 1` for every `L` (no sign hypotheses). -/
theorem abs_prodDyadicCut_le_one (L : ℝ) (j : ℕ) (y : ι → ℝ) : |prodDyadicCut L j s y| ≤ 1 := by
  rw [prodDyadicCut_def]
  split_ifs
  · rw [abs_of_nonneg (prodChi_nonneg s L)]
    exact prodChi_le_one s L
  · rw [abs_le]
    constructor <;> linarith [prodChi_le_one s (y := y) (2 ^ j * L), prodChi_nonneg s (y := y) (2 ^ j * L),
      prodChi_le_one s (y := y) (2 ^ (j - 1) * L), prodChi_nonneg s (y := y) (2 ^ (j - 1) * L)]

/-- Reindexing invariance: `Ψ_j` depends only on the multiset of `y`-values. -/
theorem prodDyadicCut_congr_nbij {ι' : Type*} {s' : Finset ι'} {y' : ι' → ℝ} (L : ℝ) (j : ℕ) (e : ι' → ι)
    (he : ∀ a ∈ s', e a ∈ s) (hinj : Set.InjOn e s') (hsurj : Set.SurjOn e s' s)
    (hy : ∀ a ∈ s', y (e a) = y' a) : prodDyadicCut L j s y = prodDyadicCut L j s' y' := by
  have h : ∀ R, prodChi s y R = prodChi s' y' R := fun R => by
    unfold prodChi
    exact (Finset.prod_nbij e he hinj hsurj fun a ha => by rw [hy a ha]).symm
  rw [prodDyadicCut_def, prodDyadicCut_def, h, h, h]

/-- The weight depends only on the values on its index set. -/
theorem prodDyadicCut_congr {y' : ι → ℝ} (L : ℝ) (j : ℕ) (hy : ∀ a ∈ s, y a = y' a) :
    prodDyadicCut L j s y = prodDyadicCut L j s y' := by
  have h : ∀ R, prodChi s y R = prodChi s y' R := fun R =>
    Finset.prod_congr rfl fun a ha => by rw [hy a ha]
  rw [prodDyadicCut_def, prodDyadicCut_def, h, h, h]

end ProdCut


end XChain.ProductCut

end WaveTurbulence
