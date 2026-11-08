/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RNode
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedRed

/-! # B3s-HELPER3: the relaxed pinned reconstruction identity (relaxed PRED, part 2)

The twin of `MkSlots.PRedRed` on RELAXED domains: the garden integrand lives on main's `kDomainFix` of the
reconstruction, the core integrand on `coreTimeDomainWR`, the native integrands on `nativeDomainWR`.

* `nativeKernelIntegrandNR` (relaxed native integrand), `coreKernelIntegrandWR`;
* **`kernelAllIntegrandD_reconstruction`**: main's `kernelAllIntegrandN_reconstruction` with the relaxed domains, for
  every `τ` on the pinned slice with free times distinct from the pins (`PinnedAt`), under `RelaxPins`; its proof is
  main's with the set identity `mem_kDomainFix_reconstruction_iff`;
* `splitIntegrandR`, **`integral_kernelAllIntegrandD_reconstruction_fix`**: the pinned time factorization (the
  pointwise identity holds `fixMeasure`-a.e., which is all the measure-preserving split needs), integrability and the
  L¹ bound of the reduced integrand. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlotsB
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.MkSlots

/-! ### The relaxed native and core integrands -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The relaxed native integrand of a replacement slot (main's `nativeKernelIntegrandN` on `nativeDomainWR`). -/
def nativeKernelIntegrandNR :
    (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s → NativeTimeBlock D s → ℂ
  | .inl p, ρ => kernelAllIntegrandD L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => A ((nativeCoupleForest D hS p).nodeEmbedding a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inl p)) (k₀ + latticePoint L (κ (p.firstLeaf hS).toNode)) ρ
  | .inr b, ρ => kernelAllIntegrandD L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => A (chainContextNode D hS b a))
      (nativeDomainWR D hS layer hLayer tt τ fixG (.inr b)) (k₀ + latticePoint L (κ b.toNode)) ρ

theorem nativeKernelIntegrandNR_eq_factors (s : ReplacementSlot S) (ρ : NativeRelativeDecoration D hS d s)
    (t : NativeTimeBlock D s) :
    nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀ κ τ fixG s ρ t =
      nativeEpsilonFactor D hS s ρ * (nativeDomainWR D hS layer hLayer tt τ fixG s).indicator
        (nativePhaseFactor D hS L γ δ k₀ κ s ρ) t * nativeInputFactorN D hS L A k₀ κ s ρ := by
  cases s <;> rfl

/-- The relaxed core integrand. -/
def coreKernelIntegrandWR (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) : ℂ :=
  (epsDec S κ : ℂ) *
    (coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)).indicator
      (phaseProd L γ δ S (cosetDecoration S L k₀ κ)) τ

end Native

/-! ### The relaxed literal integrand identity -/

section Identity

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

/-- The garden integrand on the relaxed domain of the reconstruction. -/
abbrev gardenIntegrandR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (GBranch (D.forest hS) → ℝ) → ℂ :=
  kernelAllIntegrandD L γ δ (layeredReconstruction D hS layer hLayer) A
    (kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG) k₀ κ

/-- **The relaxed literal integrand identity** (main's `kernelAllIntegrandN_reconstruction` on relaxed domains). -/
theorem kernelAllIntegrandD_reconstruction (hP : RelaxPins layer tt fixG) {n : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch (D.forest hS) → ℝ)
    (hτ : PinnedAt fixG τ) :
    gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ =
      coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) *
        ∏ s : ReplacementSlot S, nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀
          (collapseGenDecoration D hS κ).1 (nativeCoreClock D hS τ) fixG s
          (restrictRelativeDecorations D hS κ s) (nativeTimeRestriction D hS τ s) := by
  classical
  let κS := collapseGenDecoration D hS κ
  let ρ := restrictRelativeDecorations D hS κ
  let τS := nativeCoreClock D hS τ
  let τN := nativeTimeRestriction D hS τ
  let E := fun s => nativeEpsilonFactor D hS s (ρ s)
  let P := fun s => nativePhaseFactor D hS L γ δ k₀ κS.1 s (ρ s) (τN s)
  let I := fun s => nativeInputFactorN D hS L A k₀ κS.1 s (ρ s)
  let Ac := τS ∈ coreTimeDomainWR (fun b => layer (D.coreBranch hS b).toNode) tt (fixCore D hS fixG)
  let B := fun s => τN s ∈ nativeDomainWR D hS layer hLayer tt τS fixG s
  let Pc := phaseProd L γ δ S (cosetDecoration S L k₀ κS.1) τS
  have hd := mem_kDomainFix_reconstruction_iff D hS layer hLayer tt fixG hP τ hτ
  have hm : (if τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG
      then Pc * ∏ s, P s else 0) = (if Ac then Pc else 0) * ∏ s, if B s then P s else 0 :=
    (ite_congr (propext hd) (fun _ => rfl) (fun _ => rfl)).trans (mask_mul_prod Ac B Pc P)
  simp_rw [nativeKernelIntegrandNR_eq_factors]
  unfold gardenIntegrandR kernelAllIntegrandD coreKernelIntegrandWR
  simp only [Set.indicator_apply]
  change (epsDec (D.garden hS) κ.1 : ℂ) *
    (if τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG then
      phaseProd L γ δ (D.garden hS) (cosetDecoration (D.garden hS) L k₀ κ.1) τ else 0) *
      (∏ ℓ ∈ inputLeaves (D.garden hS), (A ℓ.toNode
        (cosetDecoration (D.garden hS) L k₀ κ.1 ℓ.toNode) : ℂ)) = _
  rw [epsilon_relative_reconstruction D hS κ, phaseProd_relative_reconstruction D hS L γ δ k₀ κ τ,
    inputProduct_relative_reconstructionN D hS L A k₀ κ]
  change ((epsDec S κS.1 : ℂ) * ∏ s, E s) *
    (if τ ∈ kDomainFix (layeredReconstruction D hS layer hLayer) (fun b => tt b.1.1) fixG
      then Pc * ∏ s, P s else 0) * (∏ s, I s) =
      ((epsDec S κS.1 : ℂ) * (if Ac then Pc else 0)) *
        ∏ s, E s * (if B s then P s else 0) * I s
  rw [hm, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-! ### The pinned time factorization -/

/-- The product form of the integrand on the split time coordinates. -/
def splitIntegrandR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl)
    (x : (GBranch S.tree → ℝ) × ((s : ReplacementSlot S) → NativeTimeBlock D s)) : ℂ :=
  coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG (collapseGenDecoration D hS κ).1 x.1 *
    ∏ s : ReplacementSlot S, nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀
      (collapseGenDecoration D hS κ).1 x.1 fixG s (restrictRelativeDecorations D hS κ s) (x.2 s)

/-- The reduced integrand: the core integrand times the pinned native integrals. -/
def reducedDecorationIntegrandNFR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  coreKernelIntegrandWR D hS L γ δ layer tt k₀ fixG (collapseGenDecoration D hS κ).1 τ *
    ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandNR D hS L γ δ A layer hLayer tt k₀
      (collapseGenDecoration D hS κ).1 τ fixG s (restrictRelativeDecorations D hS κ s) t
        ∂(fixMeasure (fixNative D hS fixG s))

/-- The split measure of the time coordinates. -/
abbrev splitMeasure : Measure ((GBranch S.tree → ℝ) × ((s : ReplacementSlot S) → NativeTimeBlock D s)) :=
  (fixMeasure (fixCore D hS fixG)).prod (Measure.pi fun s => fixMeasure (fixNative D hS fixG s))

theorem splitIntegrandR_ae_eq (hP : RelaxPins layer tt fixG) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (fun x => gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ ((sourceNativeTimeSplit D hS).symm x))
      =ᵐ[splitMeasure D hS fixG] splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ := by
  have hmp := measurePreserving_sourceNativeTimeSplit_fix D hS fixG
  have hae : ∀ᵐ x ∂(splitMeasure D hS fixG), PinnedAt fixG ((sourceNativeTimeSplit D hS).symm x) :=
    hmp.symm.quasiMeasurePreserving.ae (ae_pinnedAt fixG)
  filter_upwards [hae] with x hx
  obtain ⟨τ, t⟩ := x
  have h := kernelAllIntegrandD_reconstruction D hS L γ δ A layer hLayer tt k₀ fixG hP κ
    ((sourceNativeTimeSplit D hS).symm (τ, t)) hx
  have hc := congrArg Prod.fst (sourceNativeTimeSplit_symm_clocks D hS τ t)
  have hn := congrArg Prod.snd (sourceNativeTimeSplit_symm_clocks D hS τ t)
  change nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = τ at hc
  change nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = t at hn
  rw [hc, hn] at h
  exact h

theorem integrable_gardenIntegrandR {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ) (fixMeasure fixG) :=
  integrable_kernelAllIntegrandD_fix L γ δ (layeredReconstruction D hS layer hLayer) A k₀
    (measurableSet_kDomainFix _ _ _) (kDomainFix_subset_unitBoxR _ _ _) κ

theorem integrable_splitIntegrandR (hP : RelaxPins layer tt fixG) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ) (splitMeasure D hS fixG) :=
  ((measurePreserving_sourceNativeTimeSplit_fix D hS fixG).symm.integrable_comp_of_integrable
    (integrable_gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ)).congr
    (splitIntegrandR_ae_eq D hS L γ δ A layer hLayer tt k₀ fixG hP κ)

theorem integral_splitIntegrandR_section {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) :
    (∫ t, splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ (τ, t)
        ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s))) =
      reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ := by
  unfold splitIntegrandR reducedDecorationIntegrandNFR
  dsimp only
  rw [integral_const_mul, integral_fintype_prod_eq_prod]

/-- **The relaxed pinned time factorization.** -/
theorem integral_kernelAllIntegrandD_reconstruction_fix (hP : RelaxPins layer tt fixG)
    {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ ∂(fixMeasure fixG)) =
      ∫ τ, reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ
        ∂(fixMeasure (fixCore D hS fixG)) := by
  have hmp := measurePreserving_sourceNativeTimeSplit_fix D hS fixG
  rw [← hmp.symm.integral_comp' (gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ),
    integral_congr_ae (splitIntegrandR_ae_eq D hS L γ δ A layer hLayer tt k₀ fixG hP κ),
    integral_prod _ (integrable_splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG hP κ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
    integral_splitIntegrandR_section D hS L γ δ A layer hLayer tt k₀ fixG κ τ)

theorem integrable_reducedDecorationIntegrandNFR (hP : RelaxPins layer tt fixG) {n : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ)
      (fixMeasure (fixCore D hS fixG)) :=
  (integrable_splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG hP κ).integral_prod_left.congr
    (Filter.Eventually.of_forall (integral_splitIntegrandR_section D hS L γ δ A layer hLayer tt k₀ fixG κ))

theorem integral_norm_reducedDecorationIntegrand_leNFR (hP : RelaxPins layer tt fixG) {n : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, ‖reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖
        ∂(fixMeasure (fixCore D hS fixG))) ≤
      ∫ τ, ‖gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖ ∂(fixMeasure fixG) := by
  have hmp := measurePreserving_sourceNativeTimeSplit_fix D hS fixG
  have hG := integrable_splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG hP κ
  have hr := integrable_reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG hP κ
  have hm : (∫ τ, ‖reducedDecorationIntegrandNFR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖
      ∂(fixMeasure (fixCore D hS fixG))) ≤
      ∫ τ, ∫ t, ‖splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ (τ, t)‖
        ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s)) ∂(fixMeasure (fixCore D hS fixG)) := by
    apply integral_mono_ae hr.norm hG.norm.integral_prod_left
    apply Filter.Eventually.of_forall
    intro τ
    exact (congrArg norm
      (integral_splitIntegrandR_section D hS L γ δ A layer hLayer tt k₀ fixG κ τ)).symm.trans_le
      (norm_integral_le_integral_norm _)
  have ht : (∫ τ, ∫ t, ‖splitIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ (τ, t)‖
        ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s)) ∂(fixMeasure (fixCore D hS fixG))) =
      ∫ τ, ‖gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖ ∂(fixMeasure fixG) := by
    rw [← integral_prod _ hG.norm, ← hmp.symm.integral_comp' (fun τ =>
      ‖gardenIntegrandR D hS L γ δ A layer hLayer tt k₀ fixG κ τ‖)]
    refine integral_congr_ae ?_
    filter_upwards [splitIntegrandR_ae_eq D hS L γ δ A layer hLayer tt k₀ fixG hP κ] with x hx
    rw [hx]
  exact hm.trans_eq ht

end Identity

end WaveTurbulence.Flower.MkSlotsB
