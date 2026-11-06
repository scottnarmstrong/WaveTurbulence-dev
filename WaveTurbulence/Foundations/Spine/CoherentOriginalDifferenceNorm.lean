/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppDifferenceNorm
public import WaveTurbulence.Foundations.Spine.SelectedRelativeControl
/-! The coherent phi/R comparison follows from the original two leaf-profile bounds. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

 theorem coherent_app_difference_of_original_bounds (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LG : LayeredGarden 2)
    (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H₀ H₁ : LeafProfiles 2 P.d) (C₁ ε C₂ : NNReal)
    (hbase : (C₁ : ℝ) = P.C₁) (hε : 0 < (ε : ℝ)) (hεC : ε ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (h₀ : LeafwiseControlled LG H₀ (fun _ => C₁)) (h₁ : LeafwiseControlled LG H₁ (fun _ => ε))
    (C : ℝ) (hC : 0 ≤ C)
    (hc₀ : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H₀ l.1))
    (hc₁ : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H₁ l.1))
    (hb₀ : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (H₀ l.1) ≤ ENNReal.ofReal (C * C₁))
    (hb₁ : ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (H₁ l.1) ≤ ENNReal.ofReal (C * ε))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * C) ≤ C₂)
    (hplain : LG.garden.IsPlain) (horder : LG.garden.order = 2 * n)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k =>
      LeafApp.coherentCouple P.δ LG (fun a x => H₀ a x + H₁ a x) Q q q' t s k -
        LeafApp.coherentCouple P.δ LG H₀ Q q q' t s k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (inputLeaves LG.garden).card *
        (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
          ((ε : ℝ) * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))) := by
  let Cnorm : NNReal := ⟨C * (C₁ : ℝ), mul_nonneg hC (NNReal.coe_nonneg _)⟩
  have hc (S : Finset (GLeaf LG.garden.tree)) (l) (hl : l ∈ inputLeaves LG.garden) :
      ContDiff ℝ (40 * P.d + 1 + A : ℕ) (selectLeafProfiles LG.garden S H₀ H₁ l.1) :=
    contDiff_selected_profile LG.garden S H₀ H₁ l (hc₀ l hl) (hc₁ l hl)
  refine coherent_app_difference_SNorm_le P hsource hC₁ hδ hηmax hd hη ha hp hqq' hqp hn Q LG hsize hcoh
    A m H₀ H₁ C₁ ε C₂ hbase hε hεC hC₂ h₀ h₁ (fun _ => Cnorm)
    (fun S _ l hl => hc S l hl) ?_ hplain horder D hD hchoice ?_ t s ht hs
  · intro S _ l hl
    have hsel := SNormR_selected_relative_le LG.garden S H₀ H₁ (fun _ => C₁) (fun _ => ε) C l
      (hb₀ l hl) (hb₁ l hl)
    have hlow := SNorm_mono_bound (A' := 40 * P.d + 1 + A) (B' := 40 * P.d) le_rfl (by omega) _ (Complex.ofRealCLM.contDiff.comp (hc S l hl))
      _ (mul_nonneg hC (NNReal.coe_nonneg _)) hsel
    have hB : selectLeafBounds LG.garden S (fun _ => C₁) (fun _ => ε) l.1 ≤ C₁ := by
      rw [selectLeafBounds_apply]
      split_ifs
      · exact hεC
      · rfl
    have hBR : (selectLeafBounds LG.garden S (fun _ => C₁) (fun _ => ε) l.1 : ℝ) ≤ C₁ := by exact_mod_cast hB
    exact hlow.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hBR hC))
  · intro S _ word hw a c
    exact selected_combined_profiles_controlled hd LG hplain H₀ H₁ (fun _ => C₁) (fun _ => ε) C hC C₂
      hc₀ hc₁ h₀ h₁ hb₀ hb₁ hmod S word hw a c

end WaveTurbulence.LGSpine
