/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialAbsorption
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerReg.CoherentSub
/-! FLOWER-REG: the incoherent regular couples of an arbitrary finite family, in the spatial norm.

`incoherent_sub_SNorm_absorbed` is `LGSpine.SNorm_incoherentCoupleSum_absorbed` (IncoherentSpatialAbsorption.lean)
whose proof chain `SNorm_incoherentCoupleSum_le_counted` / `_geometric` / `_absorbed` is repeated verbatim, with the
sum over `incoherentCoupleSum`'s carrier replaced by a sum over an arbitrary finite family `V` of canonical,
regular, non-coherent couples. Only the covering step changes (the carrier is not needed, no `IsTrunc`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerReg
open WaveTurbulence WaveTurbulence.LGSpine Set Finset WaveTurbulence.Reg WaveTurbulence.Links
open scoped ENNReal

theorem incoherent_sub_SNorm_le_counted (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hPC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ r ≤ p, ContDiff ℝ (40 * P.d + A : ℕ) (F r))
    (hlow : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ r ≤ p, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (F r) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
      ¬ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
        (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
          ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) *
            (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  classical
  let S : ℕ → Finset (LayeredGarden 2) := fun g => (finite_regularLayeredCouplesAt p n g).toFinset
  have hcover : ∀ LG ∈ V, ∃ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), LG ∈ S g := by
    intro LG hLG
    obtain ⟨hcan, hord, hreg, hnc⟩ := hV LG hLG
    obtain ⟨Q, hw, hQ⟩ := isRegularCouple_exists_wf_decodes LG.garden hreg
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hord
    have hg0 : 1 ≤ LG.incoherency Q.links := by
      by_contra h
      exact hnc ⟨hreg, Q, hw, hQ, by omega⟩
    have hg1 : LG.incoherency Q.links ≤ n := by
      have h := incoherency_le hQ
      omega
    refine ⟨LG.incoherency Q.links, mem_filter.mpr ⟨mem_range.mpr (by omega), hg0⟩, ?_⟩
    change LG ∈ (finite_regularLayeredCouplesAt p n (LG.incoherency Q.links)).toFinset
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨Q, hw, hsize⟩, hcan, hQ, rfl⟩
  let M : ℕ → ℝ := fun g =>
    (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) *
      (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))
  have hbound : ∀ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), ∀ LG ∈ S g,
      SNorm A (4 * m) (fun k => KQ P.L P.γ P.δ F LG t k) ≤ ENNReal.ofReal (M g) := by
    intro g hg LG hLG
    have hmem : LG ∈ regularLayeredCouplesAt p n g :=
      (finite_regularLayeredCouplesAt p n g).mem_toFinset.mp hLG
    obtain ⟨Q, hcan, hQ, hind⟩ := Set.mem_iUnion.mp hmem
    have ho : LG.garden.order = 2 * n := (size_eq_order hQ).trans Q.2.2
    have hh := incoherent_KQ_SNorm_geometric P hsource hd hL hη hp hn Q.1 Q.2.1 Q.2.2 LG hQ hcan
      (by have hg0 := (mem_filter.mp hg).2; omega) A m F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂
      t ht K hK ho (hchoice LG.garden hcan.1.1 ho)
    simpa only [M, hind] using hh
  have hM : ∀ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), 0 ≤ M g := by
    intro g _
    dsimp [M]
    have hLp : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hK8 : 0 ≤ K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hPC (pow_nonneg (mul_nonneg hPC hδ) _)) hLp) hK8
  apply SNorm_sum_le_cover_count V _ S _ M _ hcover
  · intro LG hLG
    obtain ⟨g, hg, hi⟩ := hcover LG hLG
    exact contDiff_of_SNorm_bound hA _ _ (hbound g hg LG hi)
  · intro g hg LG hi
    exact contDiff_of_SNorm_bound hA _ _ (hbound g hg LG hi)
  · exact hM
  · intro g _
    have hh := ncard_regularLayeredCouplesAt_le p n g
    rw [Set.ncard_eq_toFinset_card _ (finite_regularLayeredCouplesAt p n g)] at hh
    exact_mod_cast hh
  · exact hbound


theorem incoherent_sub_SNorm_geometric (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hPC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ r ≤ p, ContDiff ℝ (40 * P.d + A : ℕ) (F r))
    (hlow : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ r ≤ p, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (F r) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
      ¬ IsCoherentCouple LG)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal ((2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have hh := incoherent_sub_SNorm_le_counted P hsource hd hL hη hPC hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t ht K hK hchoice V hV
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  let W : ℝ := K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))
  have he : (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
      (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
        ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) * W)) =
      (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
        (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
          (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g))) * W := by
    rw [sum_mul]
    apply sum_congr rfl
    intro g _
    ring
  change _ ≤ _ * W
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (counted_incoherent_sum_le (by linarith : 0 ≤ P.L) hPC hδ p n hr) (by dsimp [W]; positivity)

theorem incoherent_sub_SNorm_absorbed (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hPC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ r ≤ p, ContDiff ℝ (40 * P.d + A : ℕ) (F r))
    (hlow : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ r ≤ p, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (F r) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
      ¬ IsCoherentCouple LG)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2)
    (hn1 : 1 ≤ n)
    (hsmall : (2 * P.C₁ * C₁) * ((12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) ≤ Real.sqrt P.δ)
    (c : ℝ)
    (hlarge : K * (C₂ : ℝ) ^ (4 * m + A) * (2 : ℝ) ^ (9 * p) *
      P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ P.L ^ (-c)) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQ P.L P.γ P.δ F LG t k) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-c)) := by
  have hh := incoherent_sub_SNorm_geometric P hsource hd hL hη (zero_le_one.trans hPC) hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t ht K hK hchoice V hV hr
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hpref := prefactor_pow_le
    (by nlinarith : 1 ≤ 2 * P.C₁ * (C₁ : ℝ))
    (by positivity : 0 ≤ (12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) hsmall hn1
  have hsqrt : Real.sqrt P.δ ^ n = P.δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ]
    congr 1
    ring
  rw [hsqrt] at hpref
  have he : (C₁ : ℝ) ^ (2 * n + 1) = (C₁ : ℝ) * ((C₁ : ℝ) ^ 2) ^ n := by
    rw [pow_succ, pow_mul]
    ring
  have halgebra :
      (2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))) =
      (2 * P.C₁ * C₁ * ((12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) ^ n) *
        (K * (C₂ : ℝ) ^ (4 * m + A) * (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) := by
    rw [he]
    simp only [mul_pow]
    have hpow : (4 : ℝ) ^ n * 8 ^ n = 32 ^ n := by rw [← mul_pow]; norm_num
    rw [← hpow]
    ring
  rw [halgebra]
  exact mul_le_mul hpref hlarge (by positivity) (Real.rpow_nonneg hδ _)

end WaveTurbulence.FlowerReg
