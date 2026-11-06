/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentOriginalDifferenceNorm
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularSpecialization
public import WaveTurbulence.Foundations.Spine.RealSpatialInputBounds
/-! Uniform-layer B2 apps: the full spatial comparison from phi and R themselves. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

 theorem coherent_constant_app_difference_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p p p Q LG) (hplain : LG.garden.IsPlain)
    (horder : LG.garden.order = 2 * n) (A m : ℕ)
    (φ R : Mom P.d → ℝ) (ε C : ℝ) (hε : 0 < ε) (hεC : ε ≤ P.C₁) (hC : 1 ≤ C)
    (hφlow : SNormR (40 * P.d) (40 * P.d) φ ≤ ENNReal.ofReal P.C₁)
    (hφhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) φ ≤ ENNReal.ofReal C)
    (hRhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) R ≤ ENNReal.ofReal ε)
    (C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂)
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * C) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hs : s ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => Q.app P.δ p (fun x => φ x + R x) t s k - Q.app P.δ p φ t s k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * n + 1) *
        (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
          (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))) := by
  let Cbase : NNReal := ⟨P.C₁, zero_le_one.trans hC₁⟩
  let Eps : NNReal := ⟨ε, hε.le⟩
  have hcφ := contDiff_real_of_SNormR_bound (by omega : 40 * P.d + 1 + A ≠ 0) φ C hφhigh
  have hcR := contDiff_real_of_SNormR_bound (by omega : 40 * P.d + 1 + A ≠ 0) R ε hRhigh
  have hRlow : SNormR (40 * P.d) (40 * P.d) R ≤ ENNReal.ofReal ε :=
    SNorm_mono_bound (by omega) (by omega) _ (Complex.ofRealCLM.contDiff.comp hcR) ε hε.le hRhigh
  have hφrel : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) φ ≤ ENNReal.ofReal (C * P.C₁) :=
    hφhigh.trans (ENNReal.ofReal_le_ofReal (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hC₁ (zero_le_one.trans hC)))
  have hRrel : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) R ≤ ENNReal.ofReal (C * ε) :=
    hRhigh.trans (ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hε.le))
  have hh := coherent_app_difference_of_original_bounds P hsource hC₁ hδ hηmax hd hη ha hp le_rfl le_rfl hn
    Q LG hsize hcoh A m (fun _ => φ) (fun _ => R) Cbase Eps C₂ rfl hε (by exact_mod_cast hεC) hC₂
    (fun _ _ => hφlow) (fun _ _ => hRlow) C (zero_le_one.trans hC) (fun _ _ => hcφ) (fun _ _ => hcR)
    (fun _ _ => hφrel) (fun _ _ => hRrel) hmod hplain horder D hD hchoice t s ht hs
  have hleft : (fun k => LeafApp.coherentCouple P.δ LG (fun _ x => φ x + R x) Q p p t s k -
      LeafApp.coherentCouple P.δ LG (fun _ => φ) Q p p t s k) =
      fun k => Q.app P.δ p (fun x => φ x + R x) t s k - Q.app P.δ p φ t s k := by
    funext k
    simp only [LeafApp.coherentCouple, ite_true, LeafApp.couple_const]
  rw [hleft, card_inputLeaves_couple LG.garden hplain horder] at hh
  exact hh

end WaveTurbulence.LGSpine
