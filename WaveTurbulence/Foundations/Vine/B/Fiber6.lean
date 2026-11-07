/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber5
import Mathlib.Tactic

/-!
# VINE-B♯: the fiber sum over the local decorations (`fiber_sum`)
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

theorem measurableSet_boxSb (layerSb : GBranch Gsb.tree → ℕ) : MeasurableSet (boxSb layerSb) := by
  unfold boxSb
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem summable_unitI (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL : L ≠ 0)
    (γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) (τ' : GBranch Gsb.tree → ℝ) (j : J) :
    Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
      Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j κ :=
  Summable.of_norm_bounded
    (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock (regionOf (blk j)) (hF j) hL _).1
    fun κ => Φ.norm_unitI_le D hS hSb L γ δ h layer hLayer base frq hF z τ' j κ

theorem fiber_sum (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ}
    (hL : L ≠ 0) (γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0) :
    ∑' κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)),
      ∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
        Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p =
    ∫ τ' : GBranch Gsb.tree → ℝ, (splicedEpsilon Gsb (Φ.hinges hd) z.1 : ℂ) *
      (openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt).indicator
        (fun τ' => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' *
          ∏ j, (Φ.recJ L γ δ base z τ' j *
            ∑' κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j),
              Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j κ)) τ' := by
  have hsm := fun j => (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock (regionOf (blk j))
    (hF j) hL (Φ.bdry L base z.1 j))
  have hK : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) :=
    ((summable_pi_prod_dep (fun j (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      unitLb (blk := blk) D hS L γ δ h layer hLayer base j κ)
      (fun j κ => unitLb_nonneg _ _ _ _ _ _ _ _ _ _ _) (fun j => (hsm j).1)).1).mul_left _
  have hsum : Summable fun κs : (∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) =>
      ∫ τ' : GBranch Gsb.tree → ℝ, ‖Φ.fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs τ'‖ := by
    refine Summable.of_nonneg_of_le (fun κs => integral_nonneg fun _ => norm_nonneg _) (fun κs => ?_) hK
    have hgi : Integrable ((boxSb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
        (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j))) :=
      (integrable_indicator_iff (measurableSet_boxSb _)).2
        (integrableOn_const (by rw [volume_boxSb]; exact ENNReal.one_ne_top))
    refine (integral_mono (Φ.integrable_fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs).norm hgi
      fun τ' => Φ.norm_fibInt_le hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs τ').trans_eq ?_
    rw [integral_indicator_const _ (measurableSet_boxSb _), Measure.real, volume_boxSb]
    simp
  simp_rw [Φ.integral_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z]
  rw [integral_tsum_of_summable_integral_norm
    (fun κs => Φ.integrable_fibInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs) hsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ' => ?_)
  by_cases hp : τ' ∈ openSb Gsb (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) tt
  · unfold fibInt
    simp only [Set.indicator_of_mem hp]
    rw [tsum_mul_left, tsum_mul_left]
    congr 2
    have hs : ∀ j, Summable fun κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j) =>
        Φ.recJ L γ δ base z τ' j * Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j κ :=
      fun j => (Φ.summable_unitI D hS hSb hL γ δ h layer hLayer base frq hF z τ' j).mul_left _
    rw [tsum_pi_prod_complex (fun j κ => Φ.recJ L γ δ base z τ' j *
      Φ.unitI D hS hSb L γ δ h layer hLayer base frq z τ' j κ) hs]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [tsum_mul_left]
  · unfold fibInt
    simp [Set.indicator_of_notMem hp]

end SpliceShape

end WaveTurbulence.VineB
