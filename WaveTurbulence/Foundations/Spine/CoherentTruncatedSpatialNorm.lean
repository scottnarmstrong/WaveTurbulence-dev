/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentUniformKernelSpatialNorm
public import WaveTurbulence.Foundations.Spine.TopRegularCount
/-! Spatial bound for the actual coherent truncation, including its intermediate-order range. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg
 theorem coherent_truncated_sum_SNorm_le (P : WTParams)
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
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (coherentCoupleSum P F (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (((((12 ^ 9) * 4 : ℕ) ^ n : ℝ)) * ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
        (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
        (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  classical
  let S := (coupleCarrier P (p + 1) (2 * n)).filter IsCoherentCouple
  let E : ℝ := (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) +
    (2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
      (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ LG ∈ S, SNorm A (4 * m) (KQ P.L P.γ P.δ F LG t) ≤ ENNReal.ofReal E := by
    intro LG hLG
    have hc := (mem_filter.mp hLG).2
    obtain ⟨hm, _, Q, hw, hQ, hi⟩ := mem_filter.mp hLG
    have hmem := (Canon.finite_truncSumC_support P (p + 1) (2 * n)).mem_toFinset.mp hm
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans hmem.2.2
    have hlayer := ((coherent_canonical_iff_regular_uniform LG p).mp ⟨hmem.1, hc⟩).2
    exact coherent_uniform_kernel_SNorm_le P hsource hL hδ hC₁ hηmax hd hη ha hp hn Q LG hsize
      (isCoherentCoupleAt_of_canonical hmem.1 hw hQ hi) hmem.1.1.1 hmem.2.2 hlayer
      A m hA F U C₂ hC₂ hU hlow hhigh hmod D hD (hchoice LG.garden hmem.1.1.1 hmem.2.2) t t ht ht
  have hh := SNorm_finset_sum_bound S (fun LG => KQ P.L P.γ P.δ F LG t) (fun _ => E)
    (fun LG hLG => contDiff_of_SNorm_bound hA _ E (hterm LG hLG)) (fun _ _ => hE) hterm
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hE
  exact_mod_cast card_coherent_carrier_le P p n

end WaveTurbulence.LGSpine
