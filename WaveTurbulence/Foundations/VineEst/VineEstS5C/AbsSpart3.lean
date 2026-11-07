/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSpart2

/-! # `SAbs` of the native S-part (V5 Step 4d part C, `hAbs`, leaf `sb`) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

section Box
variable (R : CLRegionData G S a b) (hF : HF D hG L F layer base) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
include hF

open Classical in
theorem norm_spart_le_box (σ : CLInternalTime R) :
    ‖spart D hG L γ δ F layer hLayer base S a b x (clLocalClock R t σ)‖ ≤
      (Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
        Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ)
          ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1)).indicator
        (fun _ => localBound D hG L γ δ F layer hLayer base R x) σ := by
  have h1 := norm_spart_le (hLayer := hLayer) (γ := γ) (δ := δ) R hF x (clLocalClock R t σ)
  by_cases hd : DomS (fun v => layer (D.coreBranch hG v).toNode) S a (clLocalClock R t σ)
  · rw [if_pos hd] at h1
    have hmem : σ ∈ (Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
        Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ)
          ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1)) := by
      intro v _
      have hv := hd v.1 v.2
      rw [clLocalClock_internal R t σ v] at hv
      exact ⟨hv.1.le, hv.2.1.le⟩
    rw [Set.indicator_of_mem hmem]
    exact h1
  · rw [if_neg hd] at h1
    refine h1.trans ?_
    exact Set.indicator_nonneg (fun _ _ => localBound_nonneg R x) σ

theorem integrable_spart :
    Integrable (fun σ : CLInternalTime R => spart D hG L γ δ F layer hLayer base S a b x (clLocalClock R t σ)) := by
  set Bx : Set (CLInternalTime R) := Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
    Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ)
      ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1) with hBx
  have hBm : MeasurableSet Bx := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hv1 : (volume : Measure (CLInternalTime R)) Bx = 1 := volume_box R (fun v => layer (D.coreBranch hG v).toNode)
  have hvol : (volume : Measure (CLInternalTime R)) Bx ≠ ⊤ := by rw [hv1]; exact ENNReal.one_ne_top
  have hg : Integrable (Bx.indicator fun _ => localBound D hG L γ δ F layer hLayer base R x) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hvol)
  exact hg.mono' (measurable_spart R hF x t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun σ => norm_spart_le_box (hLayer := hLayer) (γ := γ) (δ := δ) R hF x t σ)

theorem integral_norm_spart_le :
    ∫ σ : CLInternalTime R, ‖spart D hG L γ δ F layer hLayer base S a b x (clLocalClock R t σ)‖ ≤
      localBound D hG L γ δ F layer hLayer base R x := by
  set Bx : Set (CLInternalTime R) := Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
    Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ)
      ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1) with hBx
  have hBm : MeasurableSet Bx := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hv1 : (volume : Measure (CLInternalTime R)) Bx = 1 := volume_box R (fun v => layer (D.coreBranch hG v).toNode)
  have hvol : (volume : Measure (CLInternalTime R)) Bx ≠ ⊤ := by rw [hv1]; exact ENNReal.one_ne_top
  have hg : Integrable (Bx.indicator fun _ => localBound D hG L γ δ F layer hLayer base R x) :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hvol)
  calc ∫ σ : CLInternalTime R, ‖spart D hG L γ δ F layer hLayer base S a b x (clLocalClock R t σ)‖
      ≤ ∫ σ, Bx.indicator (fun _ => localBound D hG L γ δ F layer hLayer base R x) σ :=
        integral_mono (integrable_spart (hLayer := hLayer) (γ := γ) (δ := δ) R hF x t).norm hg fun σ =>
          norm_spart_le_box (hLayer := hLayer) (γ := γ) (δ := δ) R hF x t σ
    _ = localBound D hG L γ δ F layer hLayer base R x := by
        rw [integral_indicator hBm, setIntegral_const, Measure.real, hv1]
        simp

end Box

/-- **`SAbs` of the native S-part**, uniform in the exterior times and the upper boundary. -/
theorem sAbs_spart (hS : G.molecule.IsBlock S a b) (R : CLRegionData G S a b) (hF : HF D hG L F layer base) (hL : L ≠ 0) :
    SAbs R L base (fun x u => spart D hG L γ δ F layer hLayer base S a b x u)
      (baseConst D hG L γ δ F layer hLayer base R) := by
  intro t e f
  have hinj : Function.Injective fun (x : ExtS R L base e f) (p : ↥(clRegionalPairs hG S)) =>
      x.1 (p.1.firstLeaf hG).toNode := fun x x' hxx =>
    extS_ext_of_pairs hS R hG hL base e f x x' fun p hp => congrFun hxx ⟨p, hp⟩
  obtain ⟨hs, hsb⟩ := tsum_localBound_le (hLayer := hLayer) (γ := γ) (δ := δ) R hF (fun x : ExtS R L base e f => x.1) hinj
  have hle : ∀ x : ExtS R L base e f,
      ∫ σ : CLInternalTime R, ‖spart D hG L γ δ F layer hLayer base S a b x.1 (clLocalClock R t σ)‖ ≤
        localBound D hG L γ δ F layer hLayer base R x.1 := fun x =>
    integral_norm_spart_le (hLayer := hLayer) (γ := γ) (δ := δ) R hF x.1 t
  have hnn : ∀ x : ExtS R L base e f,
      0 ≤ ∫ σ : CLInternalTime R, ‖spart D hG L γ δ F layer hLayer base S a b x.1 (clLocalClock R t σ)‖ :=
    fun x => integral_nonneg fun _ => norm_nonneg _
  have hsum : Summable fun x : ExtS R L base e f =>
      ∫ σ : CLInternalTime R, ‖spart D hG L γ δ F layer hLayer base S a b x.1 (clLocalClock R t σ)‖ :=
    Summable.of_nonneg_of_le hnn hle hs
  refine ⟨fun x => integrable_spart (hLayer := hLayer) (γ := γ) (δ := δ) R hF x.1 t, hsum, ?_⟩
  exact le_trans (hsum.tsum_le_tsum hle hs) hsb

end WaveTurbulence.VineEstS5C
