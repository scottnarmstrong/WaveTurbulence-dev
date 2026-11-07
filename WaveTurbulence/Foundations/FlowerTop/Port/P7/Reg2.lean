/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialAbsorption
public import WaveTurbulence.Foundations.Spine.CoherentTruncatedSpatialGeometric
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
public import WaveTurbulence.Foundations.Spine.SpatialNormFiniteCover
public import WaveTurbulence.Foundations.Spine.RegularParity
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.IncoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.IncoherentGeometricNorm
public import WaveTurbulence.Foundations.Spine.IncoherentLayeredGeometric
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Loss
/-! FLOWER-P7: the TWO-TIME family bound for regular couples (`K*_𝒬(t,s,k)`), a port of FLOWER-REG's
`CoherentSub`/`IncoherentSub`/`Family` (copied, sha256 in COPIED-SHA256SUMS) with `KQ … t` replaced by
`KQstar … t s` and the per-couple lemmas taken at two times (`coherent_uniform_kernel_SNorm_le … t s`,
`incoherent_SNorm_geometric … t s`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine Set Finset WaveTurbulence.Reg WaveTurbulence.Links
open scoped ENNReal

theorem incoherent_KQstar_SNorm_geometric (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hwf : Q.wf = true) (hsize : Q.size = 2 * n)
    (LG : LayeredGarden 2) (hQ : Q.Decodes LG.garden) (hcan : IsCanonC (p + 1) LG)
    (hi : 1 ≤ LG.incoherency Q.links)
    (A m : ℕ) (F : ℕ → Mom P.d → ℝ) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ r ≤ p, ContDiff ℝ (40 * P.d + A : ℕ) (F r))
    (hlow : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ r ≤ p, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (F r) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K) (ho : LG.garden.order = 2 * n)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ K * 8 ^ n) :
    SNorm A (4 * m) (fun k => KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * LG.incoherency Q.links)) *
        (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have hcH : ∀ l ∈ inputLeaves LG.garden,
      ContDiff ℝ (40 * P.d + A : ℕ) (layerProfiles LG F l.1) := by
    intro l _
    rw [layerProfiles_leaf]
    exact hc _ (hcan.2.1 _)
  have hlH : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d) (40 * P.d) (layerProfiles LG F l.1) ≤ ENNReal.ofReal (C₁ : ℝ) := by
    intro l _
    rw [layerProfiles_leaf]
    exact hlow _ (hcan.2.1 _)
  have hhH : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d + A) (40 * P.d + 4 * m) (layerProfiles LG F l.1) ≤ ENNReal.ofReal (U : ℝ) := by
    intro l _
    rw [layerProfiles_leaf]
    exact hhigh _ (hcan.2.1 _)
  have hh := incoherent_SNorm_geometric P hsource hd hL hη hp hn Q hwf hsize LG hQ hcan.2.1
    le_rfl le_rfl (hcan.2.1 _) (hcan.2.1 _) hi A m (layerProfiles LG F) C₁ C₂ U hC₁ hC₂
    hcH hlH hhH hcostC₂ t s ht hts K hK ho hchoice
  have he : (fun k => coupleLeaves P.L P.γ P.δ LG (layerProfiles LG F) t s k) =
      (fun k => KQstar P.L P.γ P.δ F LG t s k) := by
    funext k
    unfold coupleLeaves KQstar
    exact kernelLeaves_layerProfiles P.L P.γ P.δ LG F _ _ k _ _
  rw [he] at hh
  exact hh


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

theorem coherent_sub_SNorm_le2 (P : WTParams)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal (((((12 ^ 9) * 4 : ℕ) ^ n : ℝ)) * ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
        (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  classical
  let E : ℝ := (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
    (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
      (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ LG ∈ V, SNorm A (4 * m) (fun k => KQstar P.L P.γ P.δ F LG t s k) ≤ ENNReal.ofReal E := by
    intro LG hLG
    obtain ⟨hcan, hord, hc⟩ := hV LG hLG
    obtain ⟨hreg, Q, hw, hQ, hi⟩ := hc
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hord
    have hlayer := ((coherent_canonical_iff_regular_uniform LG p).mp ⟨hcan, hreg, Q, hw, hQ, hi⟩).2
    exact coherent_uniform_kernel_SNorm_le P hsource hL hδ hC₁ hηmax hd hη ha hp hn Q LG hsize
      (isCoherentCoupleAt_of_canonical hcan hw hQ hi) hcan.1.1 hord hlayer
      A m hA F U C₂ hC₂ hU hlow hhigh hmod D hD (hchoice LG.garden hcan.1.1 hord) t s ht hts
  have hh := SNorm_finset_sum_bound V (fun LG k => KQstar P.L P.γ P.δ F LG t s k) (fun _ => E)
    (fun LG hLG => LGSpine.contDiff_of_SNorm_bound hA _ E (hterm LG hLG)) (fun _ _ => hE) hterm
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (coherent_family_card_le p n V hV) hE


theorem coherent_sub_SNorm_geometric2 (P : WTParams)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal ((D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A)) *
        ((P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
          (2 * P.C₁ ^ 2 * P.δ))) ^ n) := by
  have hh := coherent_sub_SNorm_le2 P hsource hL hδ hC₁ hηmax hd hη ha hp hn A m hA
    F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice t s ht hts V hV
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := coherent_spatial_absolute_le_geometric n (4 * m + A)
    (by positivity : (0 : ℝ) ≤ (((12 ^ 9) * 4 : ℕ) : ℝ)) hC₁ hδ.le hL ha.le hD
    (NNReal.coe_nonneg C₂) hn1
  simpa only [Nat.cast_pow] using hb

theorem coherent_sub_SNorm_absorbed2 (P : WTParams)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal ((D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A)) * P.δ ^ ((n : ℝ) / 2)) := by
  have hh := coherent_sub_SNorm_geometric2 P hsource hL hδ hC₁ hηmax hd hη ha hp hn hn1 A m hA
    F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice t s ht hts V hV
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



theorem incoherent_sub_SNorm_le_counted2 (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
      ¬ IsCoherentCouple LG) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
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
      SNorm A (4 * m) (fun k => KQstar P.L P.γ P.δ F LG t s k) ≤ ENNReal.ofReal (M g) := by
    intro g hg LG hLG
    have hmem : LG ∈ regularLayeredCouplesAt p n g :=
      (finite_regularLayeredCouplesAt p n g).mem_toFinset.mp hLG
    obtain ⟨Q, hcan, hQ, hind⟩ := Set.mem_iUnion.mp hmem
    have ho : LG.garden.order = 2 * n := (size_eq_order hQ).trans Q.2.2
    have hh := incoherent_KQstar_SNorm_geometric P hsource hd hL hη hp hn Q.1 Q.2.1 Q.2.2 LG hQ hcan
      (by have hg0 := (mem_filter.mp hg).2; omega) A m F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂
      t s ht hts K hK ho (hchoice LG.garden hcan.1.1 ho)
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
    exact LGSpine.contDiff_of_SNorm_bound hA _ _ (hbound g hg LG hi)
  · intro g hg LG hi
    exact LGSpine.contDiff_of_SNorm_bound hA _ _ (hbound g hg LG hi)
  · exact hM
  · intro g _
    have hh := ncard_regularLayeredCouplesAt_le p n g
    rw [Set.ncard_eq_toFinset_card _ (finite_regularLayeredCouplesAt p n g)] at hh
    exact_mod_cast hh
  · exact hbound


theorem incoherent_sub_SNorm_geometric2 (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
      ¬ IsCoherentCouple LG)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal ((2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have hh := incoherent_sub_SNorm_le_counted2 P hsource hd hL hη hPC hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t s ht hts K hK hchoice V hV
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

theorem incoherent_sub_SNorm_absorbed2 (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
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
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1))
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
    SNorm A (4 * m) (fun k => ∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-c)) := by
  have hh := incoherent_sub_SNorm_geometric2 P hsource hd hL hη (zero_le_one.trans hPC) hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t s ht hts K hK hchoice V hV hr
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



theorem norm_le_of_SNorm_le2 {d A B : ℕ} (F : Mom d → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : SNorm A B F ≤ ENNReal.ofReal C) (k : Mom d) :
    ‖F k‖ ≤ jbr k ^ (-(B : ℝ)) * C := by
  have hb := SNorm_pointwise F C hC h k
  have hpos : 0 < jbr k ^ B := pow_pos (WaveTurbulence.Induct.jbr_pos k) B
  have hd : ‖F k‖ ≤ C / (jbr k ^ B) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
  simpa only [Real.rpow_neg (WaveTurbulence.Induct.jbr_pos k).le, Real.rpow_natCast, div_eq_mul_inv, mul_comm] using hd

theorem regular_family_pointwise2 (P : WTParams)
    (hsC : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hsI : LeafwiseIncoherentDecayAt P) (hs : CoherentSmallParameters P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hC₁ : 1 ≤ P.C₁)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hn1 : 1 ≤ n)
    (m : ℕ) (hm : 0 < m) (F : ℕ → Mom P.d → ℝ) (U Kc : NNReal)
    (hKc : (1 : ℝ) ≤ Kc) (hU : (1 : ℝ) ≤ U)
    (hcF : ∀ r ≤ p, ContDiff ℝ (40 * P.d + 4 * m : ℕ) (F r))
    (hlowF : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤ ENNReal.ofReal P.C₁)
    (hhighF : ∀ r ≤ p, SNormR (40 * P.d + 4 * m) (40 * P.d + 4 * m) (F r) ≤ ENNReal.ofReal (U : ℝ))
    (hhighP : SNormR (40 * P.d + 1 + 4 * m) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + 4 * m) * U) ≤ Kc)
    (D : ℝ) (hD : 1 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ (4 * m) *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2)
    (hlargeI : D * (Kc : ℝ) ^ (4 * m + 4 * m) * (2 : ℝ) ^ (9 * p) *
      P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hts : s ∈ Icc (p : ℝ) (p + 1)) (k : Mom P.d)
    (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden) :
    ‖∑ LG ∈ V, KQstar P.L P.γ P.δ F LG t s k‖ ≤
      jbr k ^ (-(4 * m : ℝ)) * (D * P.C₁ * (Kc : ℝ) ^ (4 * m + 4 * m) + 1) * P.δ ^ ((n : ℝ) / 2) := by
  classical
  have hδ := hs.delta_pos
  have hη0 := hs.eta_pos.le
  have ha : 0 < P.gamma1 - Real.sqrt P.η :=
    lt_of_le_of_lt (by positivity : 0 ≤ 2 * P.η ^ 20) hs.exponent_reserve
  have hA : 4 * m ≠ 0 := by omega
  have hsplit := (Finset.sum_filter_add_sum_filter_not V IsCoherentCouple
    (fun LG => KQstar P.L P.γ P.δ F LG t s k)).symm
  have hcoh : ∀ LG ∈ V.filter IsCoherentCouple,
      IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsCoherentCouple LG := fun LG hLG => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hLG
    exact ⟨(hV LG h1).1, (hV LG h1).2.1, h2⟩
  have hinc : ∀ LG ∈ V.filter (fun LG => ¬ IsCoherentCouple LG),
      IsCanonC (p + 1) LG ∧ LG.garden.order = 2 * n ∧ IsRegularCouple LG.garden ∧
        ¬ IsCoherentCouple LG := fun LG hLG => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hLG
    exact ⟨(hV LG h1).1, (hV LG h1).2.1, (hV LG h1).2.2, h2⟩
  have hDnn : 0 ≤ D := by linarith
  have hcohS := coherent_sub_SNorm_absorbed2 P hsC hL hδ hC₁ hs.eta_le hd hη0 ha hp hn hn1
    (4 * m) m hA F U Kc hKc hU (hlowF p le_rfl) hhighP hmod D hDnn hchoice hs.tail_delta t s ht hts
    (V.filter IsCoherentCouple) hcoh
  have hincS := incoherent_sub_SNorm_absorbed2 P hsI hd hL hη0 hC₁ hδ.le hp hn (4 * m) m hA F
    ⟨P.C₁, by linarith⟩ Kc U (show (1 : ℝ) ≤ P.C₁ from hC₁) hKc hcF hlowF hhighF hmod t s ht hts D hDnn hchoice
    (V.filter (fun LG => ¬ IsCoherentCouple LG)) hinc hr hn1
    (incoherent_smallness_of_coherent P hC₁ hs) 0 (by simpa using hlargeI)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hKnn := NNReal.coe_nonneg Kc
  have h1 := norm_le_of_SNorm_le2 _ _ (by positivity) hcohS k
  have h2 := norm_le_of_SNorm_le2 _ _ (by positivity) hincS k
  have hcast : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
  rw [hcast] at h1 h2
  simp only [neg_zero, Real.rpow_zero, mul_one] at h2
  calc _ ≤ jbr k ^ (-(4 * (m : ℝ))) * (D * P.C₁ * (Kc : ℝ) ^ (4 * m + 4 * m) * P.δ ^ ((n : ℝ) / 2)) +
        jbr k ^ (-(4 * (m : ℝ))) * (P.δ ^ ((n : ℝ) / 2)) := add_le_add h1 h2
    _ = _ := by ring


end WaveTurbulence.FlowerP7
