/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppMarkedNorm
public import WaveTurbulence.Foundations.Spine.RelativeLeafControl
public import WaveTurbulence.Foundations.Spine.CoherentChoiceENNReal
public import WaveTurbulence.Foundations.Spine.UniformLeafSpecialization
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularSpecialization
public import WaveTurbulence.Foundations.Spine.RealSpatialInputBounds
/-! Spatial bound for a uniform-profile app, retaining fixed high-order costs. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

 theorem coherent_constant_app_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p p p Q LG) (hplain : LG.garden.IsPlain)
    (horder : LG.garden.order = 2 * n)
    (A m : ℕ) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hs : s ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => Q.app P.δ p (F p) t s k) ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  let B : NNReal := ⟨P.C₁, zero_le_one.trans hC₁⟩
  have hc := contDiff_real_of_SNormR_bound (by omega : 40 * P.d + 1 + A ≠ 0) (F p) U hhigh
  have hrel : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤
      ENNReal.ofReal ((U : ℝ) * P.C₁) :=
    hhigh.trans (ENNReal.ofReal_le_ofReal (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hC₁ (NNReal.coe_nonneg U)))
  have hb : SNormR (40 * P.d + 1 + A) (40 * P.d) (F p) ≤ ENNReal.ofReal ((U : ℝ) * P.C₁) :=
    SNorm_mono_bound le_rfl (by omega) _ (Complex.ofRealCLM.contDiff.comp hc) _ (by positivity) hrel
  have hh := coherent_app_marked_SNorm_le P hsource hC₁ hδ hηmax hd hη ha hp le_rfl le_rfl hn
    Q LG hsize hcoh A m (fun _ => F p) (fun _ => U * B) (fun _ _ => hc)
    (fun _ _ => hb) hplain horder (fun _ => B) C₂ hC₂
    (fun _ _ => zero_lt_one.trans_le hC₁) 1 D (by norm_num) (by
      simp only [leafSizeProduct, NNReal.coe_mk, prod_const, one_mul]; rfl) hchoice
    (fun word hw a c => ?_) t s ht hs
  · simpa only [LeafApp.coherentCouple, ite_true, LeafApp.couple_const, one_mul] using hh
  · apply combined_leaf_profiles_controlled_relative hd LG hplain (fun _ => F p) word a c
      (fun _ => B) C₂ U (NNReal.coe_nonneg U)
    · intro l hl
      exact hc.of_le (by exact_mod_cast (show 40 * P.d + word.length ≤ 40 * P.d + 1 + A by omega))
    · exact fun _ _ => hlow
    · intro l hl
      exact SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp hc) _ (by positivity) hrel
    · apply le_trans _ hmod
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg U)
      apply pow_le_pow_right₀ (by exact_mod_cast hd : (1 : ℝ) ≤ P.d)
      omega

end WaveTurbulence.LGSpine
