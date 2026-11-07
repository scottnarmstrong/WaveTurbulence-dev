/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsBound

/-! # Pointwise bound and measurability of the CL-local summand (V5 Step 4b)

`localBound`: the product over the regional pairs of the couple majorants at the attachment labels and over the interior
branches of the (label independent) tree majorants.  `norm_clLocalSummand_le`: the summand is bounded by `localBound` on the time
domain and vanishes off it.  `measurable_clLocalSummand`: the summand is measurable in the internal times.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Elementary
variable {w d : ℕ} {G : Garden w}

theorem abs_epsCoef_le_one' (n₁ n₂ n₃ : Fin d → ℤ) : |epsCoef n₁ n₂ n₃| ≤ 1 := by
  unfold epsCoef
  split_ifs <;> simp

theorem norm_clRegionalEpsilon_le (U : Finset (GBranch G.tree)) (κ : GNode G.tree → (Fin d → ℤ)) :
    ‖(clRegionalEpsilon G U κ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold clRegionalEpsilon
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun v _ => abs_epsCoef_le_one' _ _ _

theorem norm_phaseAtom (L γ δ : ℝ) (ζ : ℤˣ) (Ω t : ℝ) : ‖phaseAtom L γ δ ζ Ω t‖ = 1 := by
  unfold phaseAtom
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_clRegionalPhase (U : Finset (GBranch G.tree)) (L γ δ : ℝ) (k : GNode G.tree → Mom d)
    (τ : GBranch G.tree → ℝ) : ‖clRegionalPhase G U L γ δ k τ‖ = 1 := by
  unfold clRegionalPhase
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_phaseAtom _ _ _ _ _ _

theorem continuous_phaseAtom (L γ δ : ℝ) (ζ : ℤˣ) (Ω : ℝ) : Continuous (phaseAtom L γ δ ζ Ω) := by
  unfold phaseAtom
  exact Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp (by fun_prop)) continuous_const)

end Elementary

section Bounds
variable {w d : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

/-- The bound of the starred kernel of the native couple at `p`, at the attachment label `x`. -/
@[expose] noncomputable def pairBound (p : SourcePair G) (x : Fin d → ℤ) : ℝ :=
  |coupling d L γ δ| ^ (nativeCoupleLayered D hG layer hLayer p).garden.order *
    majSum L F (nativeCoupleLayered D hG layer hLayer p) base (fun _ => 0) 0 x

/-- The uniform bound of the starred kernel of the native tree at `v`. -/
@[expose] noncomputable def chainBound (v : GBranch G.tree) : ℝ :=
  |coupling d L γ δ| ^ (nativeChainLayered D hG layer hLayer v).garden.order *
    ∏ ℓ : InLeaf (nativeChainLayered D hG layer hLayer v), ∑' n, inFac L F (nativeChainLayered D hG layer hLayer v) base ℓ n

variable {D hG L γ δ F layer hLayer base}

theorem norm_KQstar_le (hF : HF D hG L F layer base) (p : SourcePair G) (x : Fin d → ℤ) (t s : ℝ) :
    ‖KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p) t s (base + latticePoint L x)‖ ≤
      pairBound D hG L γ δ F layer hLayer base p x :=
  norm_kernelK_le L γ δ F _ _ _ _ _ _ (native_couple_lone D hG layer hLayer p) (couple_hF hF p x)

theorem norm_KTstar_le (hF : HF D hG L F layer base) (v : GBranch G.tree) (x : Fin d → ℤ) (t s : ℝ) :
    ‖KTstar L γ δ F (nativeChainLayered D hG layer hLayer v) t s (base + latticePoint L x)‖ ≤
      chainBound D hG L γ δ F layer hLayer base v := by
  refine (norm_kernelK_le L γ δ F _ _ _ _ _ _ (native_chain_lone D hG layer hLayer v) (chain_hF hF v x)).trans ?_
  unfold chainBound
  exact mul_le_mul_of_nonneg_left (majSum_le L F _ base (native_chain_lone D hG layer hLayer v)
    (chain_hF_base hF v) _ _ x) (by positivity)

variable (D hG L γ δ F layer hLayer base)

/-- The bound of the local summand: the couple majorants at the labels of the regional pairs times the tree majorants. -/
@[expose] noncomputable def localBound {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (x : GNode G.tree → (Fin d → ℤ)) : ℝ :=
  (∏ p ∈ clRegionalPairs hG U, pairBound D hG L γ δ F layer hLayer base p (x (p.firstLeaf hG).toNode)) *
    ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v

variable {D hG L γ δ F layer hLayer base}

theorem localBound_nonneg {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (x : GNode G.tree → (Fin d → ℤ)) :
    0 ≤ localBound D hG L γ δ F layer hLayer base R x := by
  unfold localBound pairBound chainBound majSum
  refine mul_nonneg (Finset.prod_nonneg fun p _ => mul_nonneg (by positivity) ?_) (Finset.prod_nonneg fun v _ => ?_)
  · exact tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _
  · exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)

theorem norm_clLocalStarProduct_le {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    ‖clLocalStarProduct D hG R L γ δ F layer hLayer base x t τ‖ ≤
      localBound D hG L γ δ F layer hLayer base R x := by
  unfold clLocalStarProduct localBound
  rw [norm_mul, norm_prod, norm_prod]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => ?_))
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => ?_)) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun p _ => ?_)
  · exact norm_KQstar_le hF p _ _ _
  · exact norm_KTstar_le hF v _ _ _
  · unfold pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)

/-- The CL-local summand is bounded by `localBound` on the time domain and vanishes off it. -/
theorem norm_clLocalSummand_le {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) :
    ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ ≤
      (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
        (fun _ => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) τ := by
  classical
  unfold clLocalSummand
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, norm_mul, norm_mul, norm_clRegionalPhase, one_mul]
    calc ‖(clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ)‖ * ‖clLocalStarProduct D hG R L γ δ F layer hLayer base
          (clExtendIndices R κ.1) t τ‖
        ≤ 1 * localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) :=
          mul_le_mul (norm_clRegionalEpsilon_le _ _) (norm_clLocalStarProduct_le R hF _ _ _) (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ]
    simp

/-- The CL-local summand is measurable in the internal times. -/
theorem measurable_clLocalSummand {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration R L base boundary) :
    Measurable (fun τ : CLInternalTime R => clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ) := by
  classical
  have hphase : Measurable fun τ : CLInternalTime R => clRegionalPhase G U L γ δ
      (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (measurable_clLocalClock R t v)
  have hstar : Measurable fun τ : CLInternalTime R =>
      clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ := by
    unfold clLocalStarProduct
    refine Measurable.mul (Finset.measurable_prod _ fun p _ => ?_) (Finset.measurable_prod _ fun v _ => ?_)
    · exact measurable_KQstar_comp L γ δ F _ (native_couple_plain D hG layer hLayer p) _
        (couple_hF hF p (clExtendIndices R κ.1 (p.firstLeaf hG).toNode))
        (measurable_parentClock_local R t _) (measurable_parentClock_local R t _)
    · exact measurable_KTstar_comp L γ δ F _ (native_chain_paired D hG layer hLayer v) _
        (chain_hF hF v (clExtendIndices R κ.1 v.toNode))
        (measurable_parentClock_local R t _) (measurable_clLocalClock R t v)
  unfold clLocalSummand
  exact measurable_const.mul (Measurable.indicator (hphase.mul hstar) (measurableSet_localTimeDomain R _ t))

end Bounds

end WaveTurbulence.VineEstS4
