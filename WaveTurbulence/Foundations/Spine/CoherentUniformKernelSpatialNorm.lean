/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentConstantAppNorm
public import WaveTurbulence.Foundations.Spine.CoherentConstantErrorNorm
public import WaveTurbulence.Foundations.Spine.NormAssembly
/-! High spatial control of the actual uniform coherent kernel before summing truncations. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
 theorem coherent_uniform_kernel_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p p p Q LG) (hplain : LG.garden.IsPlain)
    (horder : LG.garden.order = 2 * n) (hlayer : ∀ a, LG.layer a = p)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D) (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (t s : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) (hs : s ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => KQstar P.L P.γ P.δ F LG t s k) ≤
      ENNReal.ofReal ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
        (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have he := coherent_uniform_error_SNorm_le P hsource hL hδ hC₁ hd hη ha hp hn Q LG hsize hcoh
    hplain horder hlayer A m F U C₂ hC₂ hlow hhigh hmod D hchoice t s ht hs
  have happ := coherent_constant_app_SNorm_le P hsource hδ hC₁ hηmax hd hη ha hp hn Q LG hsize hcoh
    hplain horder A m F U C₂ hC₂ hU hlow hhigh hmod D hchoice t s ht hs
  have hc₁ := contDiff_of_SNorm_bound hA _ _ he
  have hc₂ := contDiff_of_SNorm_bound hA _ _ happ
  have hh := SNorm_add_bound _ _ hc₁ hc₂ _ _ (by positivity) (by positivity) he happ
  have hid : (fun k => (KQstar P.L P.γ P.δ F LG t s k - Q.app P.δ p (F p) t s k) +
      Q.app P.δ p (F p) t s k) = fun k => KQstar P.L P.γ P.δ F LG t s k := by
    funext k
    exact sub_add_cancel _ _
  have heq : ((fun k => KQstar P.L P.γ P.δ F LG t s k - Q.app P.δ p (F p) t s k) +
      fun k => Q.app P.δ p (F p) t s k) = (fun k => KQstar P.L P.γ P.δ F LG t s k) := hid
  rw [heq] at hh
  convert hh using 1 <;> congr 1 <;> ring

end WaveTurbulence.LGSpine
