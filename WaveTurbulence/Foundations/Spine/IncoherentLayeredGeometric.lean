/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentGeometricNorm
public import WaveTurbulence.Foundations.Spine.CoupleSpatialRegularity
/-! Literal specialization of the high-order leafwise decay estimate to a canonical layered couple. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem incoherent_KQ_SNorm_geometric (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
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
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K) (ho : LG.garden.order = 2 * n)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ K * 8 ^ n) :
    SNorm A (4 * m) (fun k => KQ P.L P.γ P.δ F LG t k) ≤
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
    hcH hlH hhH hcostC₂ t t ht ht K hK ho hchoice
  have he : (fun k => coupleLeaves P.L P.γ P.δ LG (layerProfiles LG F) t t k) =
      (fun k => KQ P.L P.γ P.δ F LG t k) := by
    funext k
    unfold coupleLeaves KQ KQstar
    exact kernelLeaves_layerProfiles P.L P.γ P.δ LG F _ _ k _ _
  rw [he] at hh
  exact hh

end WaveTurbulence.LGSpine
