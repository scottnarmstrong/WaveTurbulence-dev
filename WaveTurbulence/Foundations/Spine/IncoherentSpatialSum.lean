/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentLayeredGeometric
public import WaveTurbulence.Foundations.Spine.RegularLayeringCount
public import WaveTurbulence.Foundations.Spine.SpatialNormFiniteCover
/-! Count and sum the actual truncated incoherent carrier in its full high-order spatial norm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg WaveTurbulence.Links
open scoped ENNReal

theorem SNorm_incoherentCoupleSum_le_counted (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
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
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n) :
    SNorm A (4 * m) (incoherentCoupleSum P F (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
        (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
          ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) *
            (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  classical
  let S : ℕ → Finset (LayeredGarden 2) := fun g => (finite_regularLayeredCouplesAt p n g).toFinset
  have hcover : ∀ LG ∈ (coupleCarrier P (p + 1) (2 * n)).filter
      (fun LG => IsRegularCouple LG.garden ∧ ¬ IsCoherentCouple LG),
      ∃ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g), LG ∈ S g := by
    intro LG hLG
    obtain ⟨hm, hreg, hnc⟩ := mem_filter.mp hLG
    have hmem := (Canon.finite_truncSumC_support P (p + 1) (2 * n)).mem_toFinset.mp hm
    obtain ⟨Q, hw, hQ⟩ := isRegularCouple_exists_wf_decodes LG.garden hreg
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hmem.2.2
    have hg0 : 1 ≤ LG.incoherency Q.links := by
      by_contra h
      exact hnc ⟨hreg, Q, hw, hQ, by omega⟩
    have hg1 : LG.incoherency Q.links ≤ n := by
      have h := incoherency_le hQ
      omega
    refine ⟨LG.incoherency Q.links, mem_filter.mpr ⟨mem_range.mpr (by omega), hg0⟩, ?_⟩
    change LG ∈ (finite_regularLayeredCouplesAt p n (LG.incoherency Q.links)).toFinset
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_iUnion.mpr ⟨⟨Q, hw, hsize⟩, hmem.1, hQ, rfl⟩
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
    positivity
  unfold incoherentCoupleSum
  apply SNorm_sum_le_cover_count _ _ S _ M _ hcover
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

end WaveTurbulence.LGSpine
