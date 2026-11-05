/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.NormScaling
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.SourceInputs
public import WaveTurbulence.Foundations.IncohInst.NormBridge
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge

/-! # Leafwise normalization (TARGET L2062-L2067)

The kernel is multilinear in the individual leaf profiles. This module reduces the per-leaf bound
`∏ B_ℓ` to the unit-bound estimate, by dividing each leaf profile by its bound; a zero bound forces
the leaf profile and the kernel to vanish. -/

public section
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.LGSpine WaveTurbulence.Fourier

/-- The kernel with an individual positive bound per leaf: homogeneity of degree one in each leaf. -/
theorem kernelLeaves_scale {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (B : (Fin w × TTree.Path) → NNReal) (hB : ∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl =
      ((leafSizeProduct LG B : ℝ) : ℂ) *
        kernelLeaves L γ δ LG (fun a x => H a x / (B a : ℝ)) up s k₀ nroot nfl := by
  unfold kernelLeaves leafSizeProduct
  have hprod : ∀ x : GNode LG.garden.tree → Mom d,
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (x ℓ.toNode) : ℂ) =
        ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
          ∏ ℓ ∈ inputLeaves LG.garden, ((H ℓ.1 (x ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : (B ℓ.1 : ℝ) ≠ 0 := (hB ℓ hℓ).ne'
    push_cast
    have hne' : ((B ℓ.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    field_simp
  have hsum : ∀ κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) =
      ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
        ((epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          ((H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ)) := by
    intro κ
    rw [hprod]
    ring
  rw [tsum_congr hsum, tsum_mul_left]
  ring

/-- A vanishing leaf profile kills the kernel. -/
theorem kernelLeaves_zero_of_leaf {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) {ℓ : GLeaf LG.garden.tree} (hℓ : ℓ ∈ inputLeaves LG.garden)
    (h0 : H ℓ.1 = fun _ => 0) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k₀ nroot nfl = 0 := by
  unfold kernelLeaves
  have : ∀ κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) = 0 := by
    intro κ
    rw [Finset.prod_eq_zero hℓ (by simp [h0]), mul_zero]
  simp [this]

/-- The order-`Λ₁` spatial norm vanishing forces the function to vanish. -/
theorem eq_zero_of_spatialNorm_le_zero {d : ℕ} (Λ₁ Λ₂ : ℕ) (f : Mom d → ℂ)
    (h : spatialNorm Λ₁ Λ₂ f ≤ 0) : f = fun _ => 0 := by
  classical
  have hc : Λ₁ = 0 ∨ ContDiff ℝ Λ₁ f := by
    by_contra hn
    unfold spatialNorm at h
    rw [ite_eq_right hn] at h
    simp at h
  have h0 : momentumSupNorm Λ₂ f ≤ 0 := by
    refine le_trans ?_ h
    unfold spatialNorm
    rw [ite_eq_left hc]
    refine le_iSup₂_of_le 0 (Nat.zero_le _) ?_
    exact le_iSup_of_le (fun i => i.elim0) (by simp [momentumDerivative_zero])
  funext k
  have hk : ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖f k‖ₑ ≤ 0 :=
    le_trans (le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖f k‖ₑ) k) h0
  have hpos : ENNReal.ofReal (momentumBracket k ^ Λ₂) ≠ 0 := by
    have : 0 < momentumBracket k ^ Λ₂ := by
      unfold momentumBracket; positivity
    simpa using this
  have := (mul_eq_zero.mp (le_antisymm hk bot_le)).resolve_left hpos
  simpa using this

theorem mixedFourierNorm_zero_fun {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) :
    mixedFourierNorm θ Λ₁ Λ₂ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) = 0 := by
  classical
  have hmt : ∀ ξ : Fin r → ℝ, mixedTimeFourier (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) ξ =
      fun _ => 0 := by
    intro ξ
    funext k
    unfold mixedTimeFourier
    simp
  have hadm : MixedFourierAdmissible Λ₁ (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) := by
    refine ⟨fun k => integrable_zero _ _ _, Or.inr ?_⟩
    filter_upwards with ξ
    rw [hmt ξ]
    exact contDiff_const
  unfold mixedFourierNorm
  rw [ite_eq_left hadm]
  simp only [hmt, ENNReal.iSup_eq_zero]
  intro n _ ρ
  have : momentumDerivative ρ (fun _ : Mom d => (0 : ℂ)) = fun _ => 0 := by
    funext k
    unfold momentumDerivative
    simp
  simp [this, momentumSupNorm]

theorem mixedRestrictionNorm_zero_fun {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ))
    (K : Set (Mom d)) :
    mixedRestrictionNorm θ Λ₁ Λ₂ B K (fun _ _ => (0 : ℂ)) = 0 := by
  apply le_antisymm _ bot_le
  unfold mixedRestrictionNorm
  refine (iInf₂_le (fun (_ : Fin r → ℝ) (_ : Mom d) => (0 : ℂ)) (fun _ _ => rfl)).trans ?_
  exact (mixedFourierNorm_zero_fun θ Λ₁ Λ₂).le

/-- Reduction of the per-leaf estimate to the unit-bound estimate, for any kernel that is homogeneous
in the leaf profiles and vanishes when one leaf profile does. -/
theorem leafwise_bound_of_normalized {w d : ℕ} (LG : LayeredGarden w)
    (Kf : LeafProfiles w d → (Fin 2 → ℝ) → Mom d → ℂ)
    (hscale : ∀ (B : (Fin w × TTree.Path) → NNReal) (H : LeafProfiles w d),
      (∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ)) →
        ∀ ts k, Kf H ts k = ((leafSizeProduct LG B : ℝ) : ℂ) *
          Kf (fun a x => H a x / (B a : ℝ)) ts k)
    (hzero : ∀ (H : LeafProfiles w d) (ℓ : GLeaf LG.garden.tree), ℓ ∈ inputLeaves LG.garden →
      H ℓ.1 = (fun _ => 0) → ∀ ts k, Kf H ts k = 0)
    (η : ℝ) (J W : ℕ) (hJ : J ≠ 0) (E : Set (Fin 2 → ℝ)) (R : ℝ≥0∞)
    (hdec : ∀ H' : LeafProfiles w d,
      (∀ ℓ ∈ inputLeaves LG.garden,
        spatialNorm (40 * d) (40 * d) (fun k => (H' ℓ.1 k : ℂ)) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm η J W E univ
        (fun (t : E) (k : (univ : Set (Mom d))) => Kf H' t.1 k.1) ≤ R)
    (H : LeafProfiles w d) (B : (Fin w × TTree.Path) → NNReal) (hctrl : LeafwiseControlled LG H B) :
    XNormRestr η J W E univ (fun ts k => Kf H ts k) ≤ ENNReal.ofReal (leafSizeProduct LG B) * R := by
  refine (IncohInst.XNormRestr_le_mixed hJ η E univ _).trans ?_
  by_cases hz : ∃ ℓ ∈ inputLeaves LG.garden, B ℓ.1 = 0
  · obtain ⟨ℓ, hℓ, hB0⟩ := hz
    have hn := hctrl ℓ hℓ
    rw [hB0, NNReal.coe_zero, ENNReal.ofReal_zero, NormBridgeScratch.SNormR_eq_spatialNorm] at hn
    have h0 := eq_zero_of_spatialNorm_le_zero _ _ _ hn
    have hH0 : H ℓ.1 = fun _ => 0 := by
      funext k
      have := congrFun h0 k
      simpa using this
    have hK : (fun (t : E) (k : (univ : Set (Mom d))) => Kf H t.1 k.1) = fun _ _ => 0 := by
      funext t k
      exact hzero H ℓ hℓ hH0 _ _
    rw [hK, mixedRestrictionNorm_zero_fun]
    exact bot_le
  · push Not at hz
    have hBpos : ∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ) := fun ℓ hℓ =>
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hz ℓ hℓ))
    have hcpos : 0 < leafSizeProduct LG B := Finset.prod_pos hBpos
    have hK : (fun (t : E) (k : (univ : Set (Mom d))) => Kf H t.1 k.1) =
        fun t k => ((leafSizeProduct LG B : ℝ) : ℂ) •
          Kf (fun a x => H a x / (B a : ℝ)) t.1 k.1 := by
      funext t k
      rw [hscale B H hBpos, smul_eq_mul]
    rw [hK]
    refine (mixedRestrictionNorm_smul_le η J W E univ hcpos _).trans ?_
    refine mul_le_mul_right ?_ _
    apply hdec
    intro ℓ hℓ
    have hn := hctrl ℓ hℓ
    rw [NormBridgeScratch.SNormR_eq_spatialNorm] at hn
    have hBne : ((B ℓ.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hBpos ℓ hℓ).ne'
    have hfun : (fun k => ((H ℓ.1 k / (B ℓ.1 : ℝ) : ℝ) : ℂ)) =
        fun k => (((B ℓ.1 : ℝ) : ℂ))⁻¹ • ((H ℓ.1 k : ℝ) : ℂ) := by
      funext k
      push_cast
      rw [smul_eq_mul]
      field_simp
    show spatialNorm (40 * d) (40 * d) (fun k => (((H ℓ.1 k / (B ℓ.1 : ℝ) : ℝ)) : ℂ)) ≤ _
    rw [hfun, spatialNorm_smul _ _ (inv_ne_zero hBne)]
    calc ‖(((B ℓ.1 : ℝ) : ℂ))⁻¹‖ₑ * spatialNorm (40 * d) (40 * d) (fun k => ((H ℓ.1 k : ℝ) : ℂ))
        ≤ ENNReal.ofReal (B ℓ.1 : ℝ)⁻¹ * ENNReal.ofReal (B ℓ.1 : ℝ) := by
          gcongr
          · rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hBpos ℓ hℓ).le]
      _ = ENNReal.ofReal 1 := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hBpos ℓ hℓ).le),
            inv_mul_cancel₀ (hBpos ℓ hℓ).ne']

end WaveTurbulence.IncohLeafwise
