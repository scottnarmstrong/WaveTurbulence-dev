/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Loss
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Reg2
public import WaveTurbulence.Foundations.Spine.RegularParity
public import WaveTurbulence.Foundations.Spine.CoupleZeroRemainder
public import WaveTurbulence.Foundations.XChain.LeafPairKernel
public import WaveTurbulence.Foundations.Spine.CoherentCarrier
/-! FLOWER-P7: `RegularFamilyBound` from FLOWER-REG's `regular_family_pointwise` (positive even orders) and the
explicit order-zero couple (a single trivial couple at layer `p`, `K = F_p`); regular couples have even order. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem KQstar_order_zero {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {p : ℕ} (LG : LayeredGarden 2)
    (hcan : IsCanonC (p + 1) LG) (ho : LG.garden.order = 0) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ F LG t s k = (F p k : ℂ) := by
  have hc : IsCouple LG.garden := hcan.1
  have hcoh := coherent_of_couple_order_zero LG hc ho
  have hl : ∀ a, LG.layer a = p := coherent_canonical_layer_eq hcan hcoh
  have ht : ∀ j, LG.garden.tree j = TTree.leaf := tree_leaf_of_garden_order_zero LG.garden ho
  have he := kernelK_leafPair L γ δ F LG ht hc.1 p hl (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0
  have hz : latticePoint L (0 : Fin d → ℤ) = 0 := by
    ext j
    change ((0 : ℤ) : ℝ) / L = 0
    simp only [Int.cast_zero, zero_div]
  simpa only [KQstar, ite_true, hz, add_zero] using he

theorem order_zero_unique {p : ℕ} (LG LH : LayeredGarden 2) (hG : IsCanonC (p + 1) LG) (hH : IsCanonC (p + 1) LH)
    (hoG : LG.garden.order = 0) (hoH : LH.garden.order = 0) : LG = LH := by
  have h1 := WaveTurbulence.Reg.carrier_unique (trivial_decodes_of_couple_zero LG.garden hG.1 hoG)
    (trivial_decodes_of_couple_zero LH.garden hH.1 hoH)
  exact layered_eq_of_garden_eq_uniform h1 (coherent_canonical_layer_eq hG (coherent_of_couple_order_zero LG hG.1 hoG))
    (coherent_canonical_layer_eq hH (coherent_of_couple_order_zero LH hH.1 hoH))

theorem KQ_order_zero_family {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) {p : ℕ} (V : Finset (LayeredGarden 2))
    (hV : ∀ LG ∈ V, IsCanonC (p + 1) LG ∧ LG.garden.order = 0) (t s : ℝ) (k : Mom d) :
    ‖∑ LG ∈ V, KQstar L γ δ F LG t s k‖ ≤ |F p k| := by
  classical
  have hcard : V.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb =>
    order_zero_unique a b (hV a ha).1 (hV b hb).1 (hV a ha).2 (hV b hb).2
  rw [Finset.sum_congr rfl fun LG hLG => KQstar_order_zero L γ δ F LG (hV LG hLG).1 (hV LG hLG).2 t s k,
    Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  have : (V.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  nlinarith [abs_nonneg (F p k)]

theorem abs_inputsF_le (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hδ : 0 < P.δ) {p : ℕ} (hp : p < P.D)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) (htime : P.τstar = (P.D : ℝ) * P.δ) {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Set.Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ) (k : Mom P.d) :
    |inputsF P R p k| ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * (Cφ + 1) := by
  have hj : 0 < jbr k := WaveTurbulence.Induct.jbr_pos k
  have h4 : 4 * P.Lambda (p + 1) ≤ P.Lambda p := four_Lambda_next_le P hd hp
  have h0 : P.Lambda p ≤ P.Lambda 0 := by
    unfold WTParams.Lambda
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hexp : ∀ q : ℕ, 4 * P.Lambda (p + 1) ≤ q → jbr k ^ (-(q : ℝ)) ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
    intro q hq
    apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr k)
    have : ((4 * P.Lambda (p + 1) : ℕ) : ℝ) ≤ q := by exact_mod_cast hq
    push_cast at this
    linarith
  have hτ : P.δ * (p : ℝ) ∈ Set.Icc (0 : ℝ) P.τstar := by
    refine ⟨by positivity, ?_⟩
    rw [htime]
    have : (p : ℝ) ≤ P.D := by exact_mod_cast hp.le
    nlinarith
  have hphi := SNormR_pointwise (P.φ (P.δ * p)) Cφ hCφ (hφ _ hτ) k
  have hRn : 0 ≤ P.L ^ (-P.theta p) := Real.rpow_nonneg (by linarith) _
  have hRs := SNormR_pointwise (R p) (P.L ^ (-P.theta p)) hRn (hR p le_rfl) k
  have hLt : P.L ^ (-P.theta p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.2 (theta_nonneg P p))
  have hj0 : 0 ≤ jbr k ^ (-(P.Lambda p : ℝ)) := Real.rpow_nonneg hj.le _
  unfold inputsF
  calc |P.φ (P.δ * p) k + R p k| ≤ |P.φ (P.δ * p) k| + |R p k| := abs_add_le _ _
    _ ≤ Cφ * jbr k ^ (-(P.Lambda 0 : ℝ)) + P.L ^ (-P.theta p) * jbr k ^ (-(P.Lambda p : ℝ)) := add_le_add hphi hRs
    _ ≤ Cφ * jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) + 1 * jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hexp _ (h4.trans h0)) hCφ
        · exact mul_le_mul hLt (hexp _ h4) hj0 zero_le_one
    _ = _ := by ring

/-- The premises of `FlowerReg.regular_family_pointwise` for a fixed stage `p` (as assembled in
`FlowerReg.regularCouplesL0_of_leafwise`), plus the order-zero bound. -/
structure RegPremises (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p : ℕ) where
  hsC : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L}
  hsI : LeafwiseIncoherentDecayAt P
  hs : CoherentSmallParameters P
  hd : 1 ≤ P.d
  hL : 1 ≤ P.L
  hC₁ : 1 ≤ P.C₁
  hp : p < P.D
  hm : 0 < P.Lambda (p + 1)
  U : NNReal
  Kc : NNReal
  hKc : (1 : ℝ) ≤ Kc
  hU : (1 : ℝ) ≤ U
  hcF : ∀ r ≤ p, ContDiff ℝ (40 * P.d + 4 * P.Lambda (p + 1) : ℕ) (F r)
  hlowF : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤ ENNReal.ofReal P.C₁
  hhighF : ∀ r ≤ p, SNormR (40 * P.d + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1)) (F r) ≤
    ENNReal.ofReal (U : ℝ)
  hhighP : SNormR (40 * P.d + 1 + 4 * P.Lambda (p + 1)) (40 * P.d + 4 * P.Lambda (p + 1)) (F p) ≤
    ENNReal.ofReal (U : ℝ)
  hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * P.Lambda (p + 1))) *
    ((P.d : ℝ) ^ (40 * P.d + 4 * P.Lambda (p + 1)) * U) ≤ Kc
  D : ℝ
  hD : 1 ≤ D
  hchoice : ∀ n : ℕ, ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
    ((inputLeaves G).card + 1 : ℝ) ^ (4 * P.Lambda (p + 1)) *
      (Fintype.card (RootWeightChoices G P.d (P.Lambda (p + 1))) : ℝ) ≤ D * 8 ^ n
  hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2
  hlargeI : D * (Kc : ℝ) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) * (2 : ℝ) ^ (9 * p) *
    P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1
  C0 : ℝ
  hC0 : 0 ≤ C0
  h0 : ∀ k : Mom P.d, |F p k| ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * C0

/-- The regular-family constant. -/
noncomputable def RegPremises.Creg {P : WTParams} {F : ℕ → Mom P.d → ℝ} {p : ℕ} (H : RegPremises P F p) : ℝ :=
  max H.C0 (H.D * P.C₁ * (H.Kc : ℝ) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) + 1)

theorem RegPremises.creg_pos {P : WTParams} {F : ℕ → Mom P.d → ℝ} {p : ℕ} (H : RegPremises P F p) :
    1 ≤ H.Creg := by
  refine le_trans ?_ (le_max_right _ _)
  have h1 := H.hD; have h2 := H.hC₁; have h3 : (0 : ℝ) ≤ (H.Kc : ℝ) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) :=
    pow_nonneg (by linarith [H.hKc]) _
  have : 0 ≤ H.D * P.C₁ * (H.Kc : ℝ) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) := by positivity
  linarith

theorem RegPremises.bound {P : WTParams} {F : ℕ → Mom P.d → ℝ} {p : ℕ} (H : RegPremises P F p) :
    RegularFamilyBound P F p (fun _ => H.Creg) := by
  classical
  intro N' hN' t s ht hts k V hV
  have hδ := H.hs.delta_pos
  have hCr := H.creg_pos
  have hjb : 0 ≤ jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) := Real.rpow_nonneg (WaveTurbulence.Induct.jbr_pos k).le _
  have hδp : ∀ x : ℝ, 0 ≤ P.δ ^ x := fun x => Real.rpow_nonneg hδ.le x
  by_cases hVe : V = ∅
  · rw [hVe, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hjb (by linarith)) (hδp _)
  obtain ⟨LG, hLG⟩ := Finset.nonempty_iff_ne_empty.2 hVe
  obtain ⟨hcan, hord, hreg⟩ := hV LG hLG
  obtain ⟨n, hn⟩ := even_order_of_regular LG.garden hreg
  have hN2 : N' = n + n := by rw [← hord]; exact hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hN0 : N' = 0 := by omega
    subst hN0
    have := KQ_order_zero_family P.L P.γ P.δ F V (fun LG hLG => ⟨(hV LG hLG).1, (hV LG hLG).2.1⟩) t s k
    refine this.trans ?_
    refine (H.h0 k).trans ?_
    simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hjb
  · have hn1 : 1 ≤ n := hpos
    have hnN : n ≤ P.N (p + 1) ^ 4 := by omega
    have key := regular_family_pointwise2 P H.hsC H.hsI H.hs H.hd H.hL H.hC₁ H.hp hnN hn1
      (P.Lambda (p + 1)) H.hm F H.U H.Kc H.hKc H.hU H.hcF H.hlowF H.hhighF H.hhighP H.hmod H.D H.hD
      (H.hchoice n) H.hr H.hlargeI t s ht hts k V (fun LG hLG => by
        obtain ⟨a, b, c⟩ := hV LG hLG
        exact ⟨a, by omega, c⟩)
    refine key.trans ?_
    have hexp : (n : ℝ) / 2 = ((n + n : ℕ) : ℝ) / 4 := by push_cast; ring
    rw [hexp, hN2]
    have hmax : H.D * P.C₁ * (H.Kc : ℝ) ^ (4 * P.Lambda (p + 1) + 4 * P.Lambda (p + 1)) + 1 ≤ H.Creg :=
      le_max_right _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hjb) (hδp _)

end WaveTurbulence.FlowerP7
