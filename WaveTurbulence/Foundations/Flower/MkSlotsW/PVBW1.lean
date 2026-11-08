/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PVB1
public import WaveTurbulence.Foundations.Flower.MkUnitsL.GenW1

/-! # B3s-HELPER: pinned VINE-B♯ with unit top weights (1/4) — the pinned skeleton value

Pinned twin of `MkUnitsL/GenW*` (B3-2's generic VINE-B♯ with a slot family `Fs : SlotFamW S d` carrying unit top
weights `Fs.tw`), built on B3s's pinning technique `MkSlots/PVB*`.

The generic VINE-B♯ chain integrates against Lebesgue measure on three families of times:
* the skeleton times `GBranch S.tree → ℝ` (`skelValW`, `skelTermW`, `modeGW`) — pinned: `fixMeasure fixS`;
* the `G_sb` times (`outerValM`, `fibIntGW`, first factor of `psiIntGW`) — pinned: `fixMeasure fixSb` with
  `fixSb c = fixS (Φ.br c)`;
* the unit-interior times (`unitKernelMGW`, `unitIGW`) — unchanged (`volume`).
The top weights live inside the units (regional star product `starProdGW`, `unitKernelMGW`) and in the skeleton
integrand as the constant `topW blk Fs L base κ.1`; neither involves times, so the pinning touches only the core and
outer time integrals.  Everything pointwise is REUSED from `MkUnitsL` by import; the three measure steps
(`measurePreserving_timeSplit_fix`, `fixMeasure_boxQ_le`/`fixMeasure_boxSb_le`, `indicator_openSb_ae_fix`) are REUSED
from `MkSlots.PVB1`.

This file: `skelTermWF`, `skelValWF`, `skelValWF_eq`, `skelValWF_none`, `skelTermWF_eq_integral`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlotsW
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB
open WaveTurbulence.Flower.MkSlots (fixMeasure fixMeasure_none)
open WaveTurbulence.Flower.MkUnitsL (SlotFamW topW modeGW skelTermW skelValW)

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

open scoped Classical in
/-- The summand of `skelValWF` at a skeleton decoration: `MkUnitsL.skelTermW` with the core time integral against
`fixMeasure fixS`. -/
def skelTermWF (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (fixS : GBranch S.tree → Option ℝ)
    (κ : GenDecoration S d roots 0) : ℂ :=
  if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ((∏ s, Fs.fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) *
            topW blk Fs L base κ.1)) τ ∂(fixMeasure fixS) else 0

/-- **The pinned skeleton value with the units' top weights**: `MkUnitsL.skelValW` with the core time integral
against the pinned product measure `fixMeasure fixS` (Lebesgue at free branches, Dirac at pinned values). -/
def skelValWF (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (fixS : GBranch S.tree → Option ℝ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, skelTermWF blk D hS L γ δ base roots tt layer selSk Fs fixS κ

theorem skelValWF_eq (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (fixS : GBranch S.tree → Option ℝ) :
    skelValWF blk D hS L γ δ base roots tt layer selSk Fs fixS =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, skelTermWF blk D hS L γ δ base roots tt layer selSk Fs fixS κ := rfl

/-- **No pins**: the pinned skeleton term is `MkUnitsL.skelTermW`. -/
theorem skelTermWF_none (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) (κ : GenDecoration S d roots 0) :
    skelTermWF blk D hS L γ δ base roots tt layer selSk Fs (fun _ => none) κ =
      skelTermW blk D hS L γ δ base roots tt layer selSk Fs κ := by
  unfold skelTermWF skelTermW
  rw [fixMeasure_none]

/-- **No pins**: `skelValWF` is `MkUnitsL.skelValW`. -/
theorem skelValWF_none (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : SlotFamW S d) :
    skelValWF blk D hS L γ δ base roots tt layer selSk Fs (fun _ => none) =
      skelValW blk D hS L γ δ base roots tt layer selSk Fs := by
  rw [skelValWF_eq, MkUnitsL.skelValW_eq]
  simp_rw [skelTermWF_none]

open scoped Classical in
/-- The pinned skeleton term is the pinned integral of `MkUnitsL.modeGW` (cf. `MkUnitsL.skelTermW_eq_integral`). -/
theorem skelTermWF_eq_integral (blk : J → CLBlock S) (Fs : SlotFamW S d) (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (selSk : GenDecoration S d roots 0 → Prop)
    (fixS : GBranch S.tree → Option ℝ) (κ : GenDecoration S d roots 0) :
    skelTermWF blk D hS L γ δ base roots tt layer selSk Fs fixS κ =
      if selSk κ then ∫ τ, modeGW blk Fs D hS L γ δ base tt layer κ τ ∂(fixMeasure fixS) else 0 := by
  unfold skelTermWF modeGW
  split_ifs
  · rw [integral_const_mul]
  · rfl

end WaveTurbulence.Flower.MkSlotsW
