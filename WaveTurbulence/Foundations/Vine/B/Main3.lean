/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Main2
import Mathlib.Tactic

/-!
# VINE-B♯: the per-mode identity for a general `SpliceShape`

**`skelVal_modal_eq_outerValM`** (TARGET (redvine) L1954–L1973 with the lower-child slots of finding F-LOWCLOCK
routed to the unit modulations, RULINGS R58 repair (A)): for the skeleton expression `skelVal` with the modal slot
family (single modes `amp s' k · e^{πi (m_0 t + m_1 s)}` at the slots of `G_sb`, native `K*` kernels at the regional
slots of the units),
`skelVal … = outerValM G_sb … amp frq route hclk hmom (unitKernelM …)`.
The hypotheses are source-level absolute convergence data: `hF` (V5's source input summability at the profile of each
unit) and `hsum` (absolute summability of the outer amplitudes over the decorations of `G_sb`).
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

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem norm_integral_psiInt_le (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (L γ δ : ℝ) (base : Mom d) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ)
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (z : GenDecoration Gsb d roots 0)
    (κs : ∀ j, CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    ‖∫ p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))),
      Φ.psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq z κs p‖ ≤
      ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j) := by
  rw [Measure.volume_eq_prod]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hQ := measurableSet_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hv := volume_boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
  have hgi : Integrable ((boxQ (blk := blk) D hS layer (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)).indicator
      (fun _ => ampBound hSb L base amp z * ∏ j, unitLb (blk := blk) D hS L γ δ h layer hLayer base j (κs j)))
      ((volume : Measure (GBranch Gsb.tree → ℝ)).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (integrable_indicator_iff hQ).2 (integrableOn_const (by rw [hv]; exact ENNReal.one_ne_top))
  refine (integral_mono (Φ.integrable_psiInt hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs).norm hgi
    fun p => Φ.norm_psiInt_le hd D hS hSb L γ δ base h layer hLayer tt amp frq hF z κs p).trans_eq ?_
  rw [integral_indicator_const _ hQ, Measure.real, hv]
  simp

end SpliceShape

end WaveTurbulence.VineB
