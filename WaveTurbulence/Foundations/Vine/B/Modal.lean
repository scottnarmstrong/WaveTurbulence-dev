/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Hdata
public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
import Mathlib.Tactic

/-!
# VINE-B♯: the modal skeleton expression (the left-hand side of the per-mode identity)

`skelVal`: TARGET (redkg) for the skeleton `G_sk` (REGRED-LEAF `valueSel_skeleton_reduction`) with an arbitrary
slot-kernel family `Fs`: `coupling^n ζ Σ'_κ [sel κ] ε ∫_{coreTimeDomainW} phases · Π_s Fs s`.
With `Fs = slotFn` it is the skeleton expression of `valueSel` (`reducedStarProductLeaves`, `prod_slotFn`).
`modalFn`: the slot family of the per-mode identity (INTERFACE v2, R58): the outer slots (the slots of `G_sb`,
through `ι`) carry a single mode `amp s' k · e^{πi (m_0 t + m_1 s)}`, the regional slots of the units keep their
native kernel `slotFn` (the leafwise `K*`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
  {Gsb : Garden w}

open scoped Classical in
/-- **The skeleton expression** with a slot-kernel family `Fs` (TARGET (redkg), decoration restriction `selSk`). -/
noncomputable def skelVal (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
    ∑' κ : GenDecoration S d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ∏ s, Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) τ else 0

open scoped Classical in
/-- The summand of `skelVal` at a skeleton decoration. -/
noncomputable def skelTerm (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop)
    (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (κ : GenDecoration S d roots 0) : ℂ :=
  if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
      (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
        (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
          ∏ s, Fs s (slotTs hS tt τ s) (base + latticePoint L (κ.1 (slotNode hS s)))) τ else 0

theorem skelVal_eq (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (selSk : GenDecoration S d roots 0 → Prop) (Fs : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) :
    skelVal D hS L γ δ base roots tt layer selSk Fs =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, skelTerm D hS L γ δ base roots tt layer selSk Fs κ := rfl

open scoped Classical in
theorem skelVal_slotFn (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (selSk : GenDecoration S d roots 0 → Prop) (H : LeafProfiles w d) :
    skelVal D hS L γ δ base roots tt layer selSk (slotFn D hS L γ δ H layer hLayer) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
              reducedStarProductLeaves D hS L γ δ H layer hLayer tt base κ.1 τ) τ else 0 := by
  unfold skelVal
  congr 2
  funext κ
  simp_rw [prod_slotFn]

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

open scoped Classical in
/-- **The modal slot family** (INTERFACE v2): single modes at the outer slots, native kernels at the regional slots. -/
noncomputable def modalFn (hS : S.IsPlain) (hSb : Gsb.IsPlain) (D : ReconstructionData S) (L γ δ : ℝ)
    (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ :=
  fun s => if h : ∃ s', Φ.iota hS hSb s' = s then
      (fun ts k => amp (Classical.choose h) k * fsPhase (frq (Classical.choose h)) ts)
    else slotFn D hS L γ δ H layer hLayer s

theorem modalFn_iota (hS : S.IsPlain) (hSb : Gsb.IsPlain) (D : ReconstructionData S) (L γ δ : ℝ)
    (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (s' : ReplacementSlot Gsb) :
    Φ.modalFn hS hSb D L γ δ H layer hLayer amp frq (Φ.iota hS hSb s') =
      fun ts k => amp s' k * fsPhase (frq s') ts := by
  classical
  unfold modalFn
  have h : ∃ s'', Φ.iota hS hSb s'' = Φ.iota hS hSb s' := ⟨s', rfl⟩
  rw [dif_pos h]
  have := Φ.iota_inj hS hSb (Classical.choose_spec h)
  rw [this]

theorem modalFn_reg (hS : S.IsPlain) (hSb : Gsb.IsPlain) (D : ReconstructionData S) (L γ δ : ℝ)
    (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (amp : ReplacementSlot Gsb → Mom d → ℂ) (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (j : J)
    {s : ReplacementSlot S} (hs : s ∈ regSlots blk hS j) :
    Φ.modalFn hS hSb D L γ δ H layer hLayer amp frq s = slotFn D hS L γ δ H layer hLayer s := by
  classical
  unfold modalFn
  rw [dif_neg]
  rintro ⟨s', hs'⟩
  have hmem := Φ.iota_mem_outer hS hSb s'
  rw [hs'] at hmem
  exact (Finset.mem_filter.mp hmem).2 j hs

/-- The product of the modal slot kernels splits into the outer modes and the regional native kernels. -/
theorem prod_modalFn (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) (D : ReconstructionData S)
    (L γ δ : ℝ) (H : LeafProfiles w d) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (k : GNode S.tree → Mom d) :
    ∏ s, Φ.modalFn hS hSb D L γ δ H layer hLayer amp frq s (slotTs hS tt τ s) (k (slotNode hS s)) =
      (∏ s', amp s' (k (slotNode hS (Φ.iota hS hSb s')))) *
        (∏ s', fsPhase (frq s') (slotTs hS tt τ (Φ.iota hS hSb s'))) *
        ∏ j, ∏ s ∈ regSlots blk hS j, slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k (slotNode hS s)) := by
  have h1 := prod_slots (blk := blk) hS hd (fun s => Φ.modalFn hS hSb D L γ δ H layer hLayer amp frq s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  have h2 := Φ.prod_outer_iota hS hSb (fun s => Φ.modalFn hS hSb D L γ δ H layer hLayer amp frq s (slotTs hS tt τ s)
    (k (slotNode hS s)))
  rw [h1, h2]
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun s hs => ?_)
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s' _ => ?_
    rw [Φ.modalFn_iota hS hSb D L γ δ H layer hLayer amp frq s']
  · rw [Φ.modalFn_reg hS hSb D L γ δ H layer hLayer amp frq j hs]

end SpliceShape

end WaveTurbulence.VineB
