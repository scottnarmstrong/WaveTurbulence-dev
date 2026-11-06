/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentConstantDifferenceNorm
public import WaveTurbulence.Foundations.Spine.CoherentTaylorExactZero
public import WaveTurbulence.Foundations.Spine.RegularCodeSpatialSum
public import WaveTurbulence.Foundations.Spine.UniformRegularCouple
/-! Props 6.1–6.2 control the full coherent app sum in the high spatial norm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg

 theorem coherent_app_sum_sub_taylor_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (htaylor : ∀ L ≥ P.L, SourceCoherentTaylorAt {P with L := L})
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 < P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (R : Mom P.d → ℝ)
    (ε C : ℝ) (hε : 0 < ε) (hεC : ε ≤ P.C₁) (hC : 1 ≤ C)
    (hφlow : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal P.C₁)
    (hφhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (P.φ (P.δ * p)) ≤ ENNReal.ofReal C)
    (hRhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) R ≤ ENNReal.ofReal ε)
    (C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂)
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * C) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k =>
      (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (fun x => P.φ (P.δ * p) x + R x) t t k) -
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
      ENNReal.ofReal (((12 ^ 9 : ℕ) ^ n : ℝ) * ((2 : ℝ) ^ (2 * n + 1) *
        (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
          (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))))) := by
  classical
  let E : ℝ := (2 : ℝ) ^ (2 * n + 1) *
    (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
      (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))
  let f : RegCpl → Mom P.d → ℂ := fun Q k =>
    Q.app P.δ p (fun x => P.φ (P.δ * p) x + R x) t t k - Q.app P.δ p (P.φ (P.δ * p)) t t k
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have he : (fun k => (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
      Q.app P.δ p (fun x => P.φ (P.δ * p) x + R x) t t k) -
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) =
      fun k => ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n), f Q k := by
    funext k
    rw [← coherentTaylor_eq_zero_remainder P htaylor hd hη hp n t ht k]
    letI := finite_coupleCodes n
    letI := Fintype.ofFinite {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}
    simp only [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, f, Finset.sum_sub_distrib]
  rw [he]
  apply SNorm_finsum_codes_le hA n f E hE
  intro Q hwf hsize
  let LG := uniformDecodedCouple p Q
  have hcan : IsCanonC (p + 1) LG := uniformDecodedCouple_canonical p Q
  have hplain : LG.garden.IsPlain := hcan.1.1
  have horder : LG.garden.order = 2 * n := (decodedCouple_order Q).trans hsize
  have hcoh : IsCoherentCoupleAt p p p Q LG := isCoherentCoupleAt_of_canonical hcan hwf
    (uniformDecodedCouple_decodes p Q) (uniformDecodedCouple_incoherency p Q)
  exact coherent_constant_app_difference_SNorm_le P hsource hC₁ hδ hηmax hd hη.le ha hp hn Q LG hsize hcoh
    hplain horder A m (P.φ (P.δ * p)) R ε C hε hεC hC hφlow hφhigh hRhigh C₂ hC₂ hmod
    D hD (hchoice LG.garden hplain horder) t t ht ht

end WaveTurbulence.LGSpine
