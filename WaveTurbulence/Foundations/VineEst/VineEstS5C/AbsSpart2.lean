/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSpart

/-! # Pointwise, integral and measurability bounds of the native S-part `spart` (V5 Step 4d part C, `hAbs`, leaf `sb`) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

theorem norm_starProd_le (R : CLRegionData G S a b) (hF : HF D hG L F layer base) (x : GNode G.tree → (Fin d → ℤ))
    (top : ℝ) (u : GBranch G.tree → ℝ) :
    ‖starProd D hG L γ δ F layer hLayer base S a top x u‖ ≤ localBound D hG L γ δ F layer hLayer base R x := by
  unfold starProd localBound
  rw [norm_mul, norm_prod, norm_prod]
  have hint : clInteriorBranches R = S.erase a := rfl
  rw [hint]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => ?_))
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => ?_)) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_nonneg fun p _ => ?_)
  · exact norm_KQstar_le hF p _ _ _
  · exact norm_KTstar_le hF v _ _ _
  · unfold pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)

open Classical in
theorem norm_spart_le (R : CLRegionData G S a b) (hF : HF D hG L F layer base) (x : GNode G.tree → (Fin d → ℤ))
    (u : GBranch G.tree → ℝ) :
    ‖spart D hG L γ δ F layer hLayer base S a b x u‖ ≤
      (if DomS (fun v => layer (D.coreBranch hG v).toNode) S a u then
        localBound D hG L γ δ F layer hLayer base R x else 0) := by
  classical
  unfold spart
  by_cases hd : DomS (fun v => layer (D.coreBranch hG v).toNode) S a u
  · rw [if_pos hd, if_pos hd, one_mul, norm_mul, norm_mul, norm_clRegionalPhase, one_mul]
    calc ‖(clRegionalEpsilon G (S.erase b) x : ℂ)‖ * ‖starProd D hG L γ δ F layer hLayer base S a (u a) x u‖
        ≤ 1 * localBound D hG L γ δ F layer hLayer base R x :=
          mul_le_mul (norm_clRegionalEpsilon_le _ _) (norm_starProd_le R hF x _ u) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [if_neg hd, if_neg hd]; simp


theorem measurable_spart (R : CLRegionData G S a b) (hF : HF D hG L F layer base) (x : GNode G.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) :
    Measurable (fun σ : CLInternalTime R => spart D hG L γ δ F layer hLayer base S a b x (clLocalClock R t σ)) := by
  classical
  have hu : ∀ v : GBranch G.tree, Measurable fun σ : CLInternalTime R => clLocalClock R t σ v :=
    fun v => measurable_clock_fixed R t v
  have hp : ∀ y : GNode G.tree, Measurable fun σ : CLInternalTime R =>
      parentClock (clLocalClock R t σ a) (clLocalClock R t σ) y := fun y =>
    measurable_parentClock_top (α := CLInternalTime R) (fun σ => clLocalClock R t σ a) (fun σ => clLocalClock R t σ)
      (hu a) hu y
  have hset : MeasurableSet {σ : CLInternalTime R | DomS (fun v => layer (D.coreBranch hG v).toNode) S a (clLocalClock R t σ)} := by
    have : {σ : CLInternalTime R | DomS (fun v => layer (D.coreBranch hG v).toNode) S a (clLocalClock R t σ)} =
        ⋂ v ∈ S.erase a, {σ : CLInternalTime R | ((layer (D.coreBranch hG v).toNode : ℕ) : ℝ) < clLocalClock R t σ v ∧
          clLocalClock R t σ v < (layer (D.coreBranch hG v).toNode : ℕ) + 1 ∧ 0 < clLocalClock R t σ v ∧
          clLocalClock R t σ v < parentClock (clLocalClock R t σ a) (clLocalClock R t σ) v.toNode} := by
      ext σ; simp [DomS]
    rw [this]
    refine Finset.measurableSet_biInter _ fun v _ => ?_
    simp only [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (hu v)).inter ((measurableSet_lt (hu v) measurable_const).inter
      ((measurableSet_lt measurable_const (hu v)).inter (measurableSet_lt (hu v) (hp _))))
  have hphase : Measurable fun σ : CLInternalTime R =>
      clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base x) (clLocalClock R t σ) := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (hu v)
  have hstar : Measurable fun σ : CLInternalTime R =>
      starProd D hG L γ δ F layer hLayer base S a (clLocalClock R t σ a) x (clLocalClock R t σ) := by
    unfold starProd
    refine Measurable.mul (Finset.measurable_prod _ fun p _ => ?_) (Finset.measurable_prod _ fun v _ => ?_)
    · exact measurable_KQstar_comp L γ δ F _ (native_couple_plain D hG layer hLayer p) _
        (couple_hF hF p (x (p.firstLeaf hG).toNode)) (hp _) (hp _)
    · exact measurable_KTstar_comp L γ δ F _ (native_chain_paired D hG layer hLayer v) _
        (chain_hF hF v (x v.toNode)) (hp _) (hu v)
  unfold spart
  exact (Measurable.ite hset measurable_const measurable_const).mul (measurable_const.mul (hphase.mul hstar))

end WaveTurbulence.VineEstS5C
