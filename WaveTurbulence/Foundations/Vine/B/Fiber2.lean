/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber1
import Mathlib.Tactic

/-!
# VINE-B♯: measurability and the domination of `psiInt`
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The box of the interior times of unit `j`. -/
def boxU (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (blk : J → CLBlock S)
    (j : J) : Set (CLInternalTime (regionOf (blk j))) :=
  Set.pi Set.univ fun v : ↥(clInteriorBranches (regionOf (blk j))) =>
    Set.Icc ((fun v => layer (D.coreBranch hS v).toNode) v.1 : ℝ) ((fun v => layer (D.coreBranch hS v).toNode) v.1 + 1)

theorem volume_boxU (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (j : J) :
    (volume : Measure (CLInternalTime (regionOf (blk j)))) (boxU D hS layer blk j) = 1 :=
  volume_box (regionOf (blk j)) (fun v => layer (D.coreBranch hS v).toNode)

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

/-- The unit box product set `Q ⊆ (τ', (τ_j))`. -/
def boxQ (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (layerSb : GBranch Gsb.tree → ℕ) : Set ((GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) :=
  boxSb layerSb ×ˢ Set.pi Set.univ (fun j => boxU D hS layer blk j)

theorem volume_boxQ (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (layerSb : GBranch Gsb.tree → ℕ) :
    ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
      (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) (boxQ (blk := blk) D hS layer layerSb) = 1 := by
  unfold boxQ
  rw [Measure.prod_prod, volume_boxSb, volume_pi_pi]
  simp [volume_boxU]

theorem measurableSet_boxQ (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (layerSb : GBranch Gsb.tree → ℕ) : MeasurableSet (boxQ (blk := blk) D hS layer layerSb) := by
  unfold boxQ boxSb boxU
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod
    (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi fun _ => measurableSet_Icc)

theorem measurable_psiInt (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Measurable (Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs) := by
  have hg : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j) :=
    ((Φ.measurable_sbInt hS hSb L γ δ base tt amp frq z).comp measurable_fst).mul
      (Finset.measurable_prod _ fun j _ => Φ.measurable_unitInt D hS L γ δ h layer hLayer base frq hSb z j (hF j) (κs j))
  have hO : MeasurableSet (Prod.fst ⁻¹' openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt :
      Set ((GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (measurableSet_openSb _ _ _).preimage measurable_fst
  have : Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs = fun p =>
      (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Prod.fst ⁻¹' openSb Gsb
        (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
          Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
          ∏ j, Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j)) p := by
    funext p
    unfold psiInt
    simp only [Set.indicator, Set.mem_preimage]
    congr
  rw [this]
  exact measurable_const.mul (hg.indicator hO)

end SpliceShape

/-- V5's local bound of a local decoration of unit `j`. -/
noncomputable def unitLb (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) {β : Fin 4 → Mom d}
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) : ℝ :=
  localBound D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j))
    (clExtendIndices (regionOf (blk j)) κ.1)

theorem unitLb_nonneg (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) {β : Fin 4 → Mom d}
    (κ : CLLocalDecoration (regionOf (blk j)) L base β) :
    0 ≤ unitLb (blk := blk) D hS L γ δ h layer hLayer base j κ :=
  localBound_nonneg _ _

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem norm_psiInt_le (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j))
    (p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j)))) :
    ‖Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p‖ ≤
      (boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) p := by
  have hU : ∏ j, ‖Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
      (Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
        (fun _ => ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) p.2 := by
    have hj : ∀ j, ‖Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j)‖ ≤
        (boxU D hS layer blk j).indicator
          (fun _ => unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) (p.2 j) := fun j => by
      unfold unitInt
      rw [norm_mul, norm_recExp, one_mul]
      exact norm_gUnit_le (γ := γ) (hLayer := hLayer) (regionOf (blk j)) (hF j)
        (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.bdry L base z.1 j) (Φ.clocks p.1 j) (κs j) (p.2 j)
    by_cases hpi : p.2 ∈ Set.pi Set.univ fun j => boxU D hS layer blk j
    · rw [Set.indicator_of_mem hpi]
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
      have := hj j
      rwa [Set.indicator_of_mem (hpi j (Set.mem_univ j))] at this
    · rw [Set.indicator_of_notMem hpi]
      obtain ⟨j, hjn⟩ : ∃ j, p.2 j ∉ boxU D hS layer blk j := by
        by_contra hc
        push Not at hc
        exact hpi fun j _ => hc j
      have h0 : ‖Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j)‖ = 0 := by
        have := hj j
        rw [Set.indicator_of_notMem hjn] at this
        exact le_antisymm this (norm_nonneg _)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) h0]
  unfold psiInt
  by_cases hp : p.1 ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · rw [Set.indicator_of_mem hp]
    have h1 : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_splicedEpsilon_le _ _ _
    have h2 : ‖Φ.sbInt hS hSb L γ δ base tt amp frq z p.1‖ ≤ ampBound hSb L base amp z := by
      unfold sbInt ampBound
      rw [norm_mul, norm_mul, norm_phaseProd_le, norm_routedPhase, norm_prod]
      simp
    have hb : ‖(splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) * (Φ.sbInt hS hSb L γ δ base tt amp frq z p.1 *
        ∏ j, Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j (κs j) (p.2 j))‖ ≤
        ampBound hSb L base amp z * ((Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
          (fun _ => ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) p.2) := by
      rw [norm_mul, norm_mul, norm_prod]
      calc _ ≤ 1 * (ampBound hSb L base amp z * ((Set.pi Set.univ fun j => boxU D hS layer blk j).indicator
          (fun _ => ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)) p.2)) :=
            mul_le_mul h1 (mul_le_mul h2 hU (Finset.prod_nonneg fun _ _ => norm_nonneg _)
              (ampBound_nonneg _ _ _ _ _)) (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
              zero_le_one
        _ = _ := one_mul _
    by_cases hpi : p.2 ∈ Set.pi Set.univ fun j => boxU D hS layer blk j
    · have hq : p ∈ boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) :=
        ⟨openSb_subset_box _ _ hp, hpi⟩
      rw [Set.indicator_of_mem hq]
      rwa [Set.indicator_of_mem hpi] at hb
    · rw [Set.indicator_of_notMem hpi, mul_zero] at hb
      refine hb.trans ?_
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
        (Finset.prod_nonneg fun j _ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)) _
  · rw [Set.indicator_of_notMem hp]
    simp only [mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => mul_nonneg (ampBound_nonneg _ _ _ _ _)
      (Finset.prod_nonneg fun j _ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _)) _

end SpliceShape

end WaveTurbulence.VineB
