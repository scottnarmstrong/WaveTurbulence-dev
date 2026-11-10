/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Flower.Stage1WVine.GenVB2

/-! # B3s MK-SLOTS: pinned VINE-B♯ (1/4) — the pinned skeleton value and the pinned measure steps

## Plan (pinned copy-thread of `Stage1WVine/{GenVB1, GenVB2, GenVB3, GenModes, WInteg}`)

The generic VINE-B♯ chain integrates against Lebesgue measure on three families of times:
* the skeleton times `GBranch S.tree → ℝ` (`skelVal`, `skelTerm`, `modeG`) — pinned: `fixMeasure fixS`;
* the `G_sb` times `GBranch Gsb.tree → ℝ` (`outerValM`, `fibIntG`, first factor of `psiIntG`) — pinned:
  `fixMeasure fixSb` with `fixSb c = fixS (Φ.br c)` (the pins of the old names);
* the unit-interior times `CLInternalTime (regionOf (blk j))` (`unitKernelMG`, `unitIG`) — unchanged (`volume`):
  pins are never at unit-interior atoms.
Everything pointwise (all of `GenVB1`, `integrand_glueG`, `psiIntG`, `fibIntG`, `inner_psiIntG`, the unit bounds,
`unitKernelMG` and its bounds, `hasSum_modeGG`, `modeG_eq_psiG`, the decoration bounds `kBoundG`) is REUSED by import;
only the lemmas integrating over skeleton or `G_sb` times are re-proved, with three measure steps:
1. `measurePreserving_timeSplit_fix` (this file): `timeSplit` is a coordinate relabeling, so it maps `fixMeasure fixS`
   to `(fixMeasure fixSb).prod volume` — provided the unit interiors `inter blk j` are unpinned (`hU`);
2. `fixMeasure_boxSb_le`, `fixMeasure_boxQ_le` (this file): the boxes have measure `≤ 1` (a pinned factor is a Dirac
   mass `≤ 1`) — this replaces `volume_boxSb`/`volume_boxQ` in every bound;
3. `indicator_openSb_ae_fix` (this file): the closed and open spliced domains agree `fixMeasure fix`-a.e. provided no
   pinned value is an endpoint of its layer window (`hW`); the parent order and root bounds are strict in both domains,
   so nothing else is needed.
Files: `PVB1` (definitions `skelTermF`, `skelValF`, the three measure steps), `PVB2` (pinned Fubini and the per-mode
identity `skelValF (modalFnG) = outerValMμ`), `PVBModes` (the pinned mode expansion
`hasSum_skelValF_outerValMμ` and its unpinned specialization), `PVBInteg` (pinned integrability/summability of the outer
integrand). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract

namespace WaveTurbulence.Flower.MkSlots
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-! ## The pinned skeleton expression -/

/-! ## Measure step 1: the pinned time split -/

/-- Unit interiors are unpinned as soon as every atom of every unit is unpinned. -/
theorem fixU_of_atoms (fixS : GBranch S.tree → Option ℝ) (h : ∀ j, ∀ a ∈ (blk j).atoms, fixS a = none) :
    ∀ j, ∀ a ∈ inter blk j, fixS a = none :=
  fun j a ha => h j a (mem_inter.mp ha).1

/-- **The pinned time split.** If no unit-interior branch is pinned, the time split `τ ↦ (τ', (τ_j))` maps the pinned
skeleton measure to the pinned `G_sb` measure (pins of the old names `Φ.br c`) times Lebesgue measure on the unit
interiors. -/
theorem measurePreserving_timeSplit_fix (Φ : SpliceShape blk Gsb) (hd : Disj blk) (fixS : GBranch S.tree → Option ℝ)
    (hU : ∀ j, ∀ a ∈ inter blk j, fixS a = none) :
    MeasurePreserving (Φ.timeSplit hd) (fixMeasure fixS)
      ((fixMeasure (fun c => fixS (Φ.br c))).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Φ.branchSplit hd).symm).symm
      (fixMeasure fixS) (fixMeasure (fixS ∘ (Φ.branchSplit hd).symm)) :=
    (measurePreserving_piCongrLeft_fix (Φ.branchSplit hd).symm fixS).symm
  have h₂ := measurePreserving_sumPiEquivProdPi_fix (fixS ∘ (Φ.branchSplit hd).symm)
  have hl : (fixS ∘ (Φ.branchSplit hd).symm) ∘ Sum.inl = fun c => fixS (Φ.br c) := rfl
  have hr : (fixS ∘ (Φ.branchSplit hd).symm) ∘ Sum.inr = fun _ => none := by
    funext x
    exact hU x.1 x.2.1 x.2.2
  rw [hl, hr, fixMeasure_none] at h₂
  have h₃ : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (GBranch Gsb.tree → ℝ))
      (MeasurableEquiv.piCurry (fun (j : J) (_ : ↥(inter blk j)) => ℝ)))
      ((fixMeasure (fun c => fixS (Φ.br c))).prod (volume : Measure ((Σ j, ↥(inter blk j)) → ℝ)))
      ((fixMeasure (fun c => fixS (Φ.br c))).prod
        (volume : Measure (∀ j, CLInternalTime (regionOf (blk j))))) :=
    (MeasurePreserving.id _).prod (measurePreserving_piCurry_real (fun j : J => ↥(inter blk j)))
  exact h₃.comp (h₂.comp h₁)

/-! ## Measure step 2: the boxes have pinned measure at most one -/

/-- A constant on a set of measure `≤ 1` is integrable. -/
theorem integrable_indicator_const_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (h1 : μ s ≤ 1) (c : ℝ) : Integrable (s.indicator fun _ => c) μ :=
  (integrable_indicator_iff hs).2 (integrableOn_const (h1.trans_lt ENNReal.one_lt_top).ne)

/-- The integral of a nonnegative constant on a set of measure `≤ 1` is at most the constant. -/
theorem integral_indicator_const_le_of_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (h1 : μ s ≤ 1) {c : ℝ} (hc : 0 ≤ c) : ∫ x, s.indicator (fun _ => c) x ∂μ ≤ c := by
  rw [integral_indicator_const _ hs, smul_eq_mul]
  have hr : μ.real s ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (h1.trans_eq ENNReal.ofReal_one.symm)
  calc μ.real s * c ≤ 1 * c := mul_le_mul_of_nonneg_right hr hc
    _ = c := one_mul c

/-! ## Measure step 3: closed and open spliced domains agree a.e. on the pinned slice -/

end WaveTurbulence.Flower.MkSlots
