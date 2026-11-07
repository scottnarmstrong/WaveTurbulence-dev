/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH11

/-!
# S2 REPRESENTS, VINE-D (12): amplitude bounds and the mass of the expansion with vine factors

* `splicedAmplitudeBounds_DH`: every assembled mode satisfies `SplicedAmplitudeBounds` (edge amplitudes as in the
  vine-free case; the hinge amplitude is bounded by `1` and vanishes unless every hinge dart is in the unit ball of its
  centre: TARGET L1966 for `K†`).
* `tsum_norm_constWH_le`: the total weight `Σ_{ξh} ‖constWH ξh‖ ≤ Cχ^{#branches} · Π_s (slot masses) · ballCard^{|G|} ·
  Π_j Mh j`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS MeasureTheory Set
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

namespace AsmCtxH
variable (A : AsmCtxH S d)

open scoped Classical in
theorem splicedAmplitudeBounds_DH (ξh : A.Xi) : SplicedAmplitudeBounds S (A.DH ξh) := by
  have hasm := splicedAmplitudeBounds_asm A.fam A.hS A.hd A.Cχ A.hC A.hCpos A.layer0 A.gs A.tt ξh.1
  refine ⟨hasm.1, hasm.2.1, fun K => A.norm_hingeAmp_le ξh K, fun K ⟨x, hx⟩ => ?_⟩
  show A.hingeAmp ξh K = 0
  unfold hingeAmp
  have hnot : ¬ ∀ y : HingeDarts S A.hinges, ‖K y - cenS A.fam ξh.1 (slotOfDart A.hS y.1)‖ ≤ 1 :=
    fun hall => absurd (hall x) (not_le.2 hx)
  rw [if_neg hnot, mul_zero]

theorem tsum_norm_constWH_le :
    ∑' ξh : A.Xi, ENNReal.ofReal ‖A.constWH ξh‖ ≤
      ENNReal.ofReal (A.Cχ ^ (Fintype.card (GBranch S.tree))) *
        ((∏ s, ∑' l, ENNReal.ofReal (A.fam.w s l)) *
          ((nodeBallCard d ^ ∑ j, (S.tree j).order : ℕ) : ℝ≥0∞)) * ∏ j, ENNReal.ofReal (A.Mh j) :=
  A.tsum_constWH_le.trans (by gcongr; exact A.toAsmCtx.tsum_constW_le)

end AsmCtxH
end WaveTurbulence.Represents
