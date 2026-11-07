/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTruncatedSpatialGeometric
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
public import WaveTurbulence.Foundations.Spine.SpatialNormFiniteCover
public import WaveTurbulence.Foundations.Spine.RegularParity
/-! FLOWER-REG: the coherent regular couples of an arbitrary finite family, in the spatial norm.

`coherent_sub_SNorm_le` is `LGSpine.coherent_truncated_sum_SNorm_le` (CoherentTruncatedSpatialNorm.lean, copied
sha256 in COPIED-SHA256SUMS) with the sum over `coherentCoupleSum`'s carrier replaced by a sum over an arbitrary
finite family `V` of coherent canonical couples. Only the carrier and the cardinality step change; the per-couple
spatial bound is `LGSpine.coherent_uniform_kernel_SNorm_le`. There is no truncation `IsTrunc` on `V`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence WaveTurbulence.LGSpine Set Finset WaveTurbulence.Reg WaveTurbulence.Induct
open scoped ENNReal

theorem coherent_family_card_le (p n : ℕ) (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    (V.card : ℝ) ≤ (((12 ^ 9) * 4 : ℕ) ^ n : ℝ) := by
  classical
  have hsub : V ⊆ (finite_regularLayeredCouplesAt p n 0).toFinset := by
    intro LG hLG
    obtain ⟨hcan, hord, hreg, Q, hw, hQ, hi⟩ := hV LG hLG
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hord
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨Q, hw, hsize⟩, hcan, hQ, hi⟩
  have h1 : V.card ≤ (finite_regularLayeredCouplesAt p n 0).toFinset.card := card_le_card hsub
  have h2 := ncard_regularLayeredCouplesAt_le p n 0
  rw [Set.ncard_eq_toFinset_card _ (finite_regularLayeredCouplesAt p n 0)] at h2
  have h3 : V.card ≤ (12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ 0 * 2 ^ (2 * n)) := h1.trans h2
  have h4 : (12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ 0 * 2 ^ (2 * n)) = ((12 ^ 9) * 4) ^ n := by
    rw [pow_zero, one_mul, pow_mul, mul_pow]
    norm_num
  rw [h4] at h3
  exact_mod_cast h3

theorem coherent_sub_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal (((((12 ^ 9) * 4 : ℕ) ^ n : ℝ)) * ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
        (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  classical
  let E : ℝ := (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
    (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
      (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ LG ∈ V, SNorm A (4 * m) (KQ P.L P.γ P.δ F LG t) ≤ ENNReal.ofReal E := by
    intro LG hLG
    obtain ⟨hcan, hord, hc⟩ := hV LG hLG
    obtain ⟨hreg, Q, hw, hQ, hi⟩ := hc
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hord
    have hlayer := ((coherent_canonical_iff_regular_uniform LG p).mp ⟨hcan, hreg, Q, hw, hQ, hi⟩).2
    exact coherent_uniform_kernel_SNorm_le P hsource hL hδ hC₁ hηmax hd hη ha hp hn Q LG hsize
      (isCoherentCoupleAt_of_canonical hcan hw hQ hi) hcan.1.1 hord hlayer
      A m hA F U C₂ hC₂ hU hlow hhigh hmod D hD (hchoice LG.garden hcan.1.1 hord) t t ht ht
  have hh := SNorm_finset_sum_bound V (fun LG => KQ P.L P.γ P.δ F LG t) (fun _ => E)
    (fun LG hLG => LGSpine.contDiff_of_SNorm_bound hA _ E (hterm LG hLG)) (fun _ _ => hE) hterm
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (coherent_family_card_le p n V hV) hE


theorem coherent_sub_SNorm_geometric (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hn1 : 1 ≤ n)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal ((D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A)) *
        ((P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
          (2 * P.C₁ ^ 2 * P.δ))) ^ n) := by
  have hh := coherent_sub_SNorm_le P hsource hL hδ hC₁ hηmax hd hη ha hp hn A m hA
    F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice t ht V hV
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := coherent_spatial_absolute_le_geometric n (4 * m + A)
    (by positivity : (0 : ℝ) ≤ (((12 ^ 9) * 4 : ℕ) : ℝ)) hC₁ hδ.le hL ha.le hD
    (NNReal.coe_nonneg C₂) hn1
  simpa only [Nat.cast_pow] using hb

theorem coherent_sub_SNorm_absorbed (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hn1 : 1 ≤ n)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (hsmall : (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
      (2 * P.C₁ ^ 2 * P.δ)) ≤ Real.sqrt P.δ * Real.exp (-1))
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal ((D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A)) * P.δ ^ ((n : ℝ) / 2)) := by
  have hh := coherent_sub_SNorm_geometric P hsource hL hδ hC₁ hηmax hd hη ha hp hn hn1 A m hA
    F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice t ht V hV
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
      (2 * P.C₁ ^ 2 * P.δ)) := by positivity
  have hpow := pow_le_pow_left₀ hr0 (hsmall.trans (mul_le_of_le_one_right (Real.sqrt_nonneg _)
    (Real.exp_le_one_iff.mpr (by norm_num)))) n
  have hsqrt : Real.sqrt P.δ ^ n = P.δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hsqrt] at hpow
  have hD' : 0 ≤ D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A) := by
    have := NNReal.coe_nonneg C₂
    positivity
  exact mul_le_mul_of_nonneg_left hpow hD'

end WaveTurbulence.FlowerReg
