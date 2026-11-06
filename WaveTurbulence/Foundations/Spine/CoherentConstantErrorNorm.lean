/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentErrorUniform
public import WaveTurbulence.Foundations.Spine.CoherentChoiceENNReal
public import WaveTurbulence.Foundations.Spine.UniformLeafSpecialization
public import WaveTurbulence.Foundations.Spine.LeafwiseRegularSpecialization
public import WaveTurbulence.Foundations.Spine.RealSpatialInputBounds
/-! Full spatial error between a uniform-layer kernel and its literal B2 app. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

 theorem coherent_uniform_error_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p p p Q LG) (hplain : LG.garden.IsPlain)
    (horder : LG.garden.order = 2 * n) (hlayer : ∀ a, LG.layer a = p)
    (A m : ℕ) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hs : s ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => KQstar P.L P.γ P.δ F LG t s k - Q.app P.δ p (F p) t s k) ≤
      ENNReal.ofReal ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  let Cbase : NNReal := ⟨P.C₁, zero_le_one.trans hC₁⟩
  have hc := contDiff_real_of_SNormR_bound (by omega : 40 * P.d + 1 + A ≠ 0) (F p) U hhigh
  have hh := coherent_error_SNorm_uniform P hsource hL hd hη ha hp le_rfl le_rfl hn Q LG hsize hcoh
    A m (fun _ => F p) Cbase C₂ U hC₁ hC₂ (fun _ _ => hc) (fun _ _ => hlow)
      (fun _ _ => hhigh) hmod hplain t s ht hs
  have he : (fun k => coupleLeaves P.L P.γ P.δ LG (fun _ => F p) t s k -
      LeafApp.coherentCouple P.δ LG (fun _ => F p) Q p p t s k) =
      fun k => KQstar P.L P.γ P.δ F LG t s k - Q.app P.δ p (F p) t s k := by
    funext k
    rw [coupleLeaves_uniform_eq_KQstar P.L P.γ P.δ LG p hlayer F t s k]
    simp only [LeafApp.coherentCouple, ite_true, LeafApp.couple_const]
  rw [he] at hh
  have hchoice' := coherent_choice_cost_le (d := P.d) (m := m) (A := A) LG.garden hplain horder
    D P.C₁ C₂ (zero_le_one.trans hC₁) (NNReal.coe_nonneg _) hchoice
  have hfinal := hh.trans (mul_le_mul_of_nonneg_left hchoice' (by positivity))
  have hpos : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) := by positivity
  simpa only [regBound, Nat.cast_one, mul_one, ← ENNReal.ofReal_mul hpos] using hfinal

end WaveTurbulence.LGSpine
