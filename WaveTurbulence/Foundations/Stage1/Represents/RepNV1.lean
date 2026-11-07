/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.Consume
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep3
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the slot kernels of the leafwise skeleton product and the chi constant
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

/-- The leafwise native kernel of a slot as a function of its two clock times and its momentum. -/
noncomputable def slotFn (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => coupleLeaves L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (nativeCoupleProfiles D hS H p) (ts 0) (ts 1) k
  | .inr b => fun ts k => treeLeaves L γ δ (nativeChainLayered D hS layer hLayer b)
      (nativeChainProfiles D hS H b) (ts 0) (ts 1) k

theorem prod_slotFn (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ) (H : LeafProfiles w d)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    ∏ s, slotFn D hS L γ δ H layer hLayer s (slotTs hS tt τ s) (k₀ + latticePoint L (κ (slotNode hS s))) =
      reducedStarProductLeaves D hS L γ δ H layer hLayer tt k₀ κ τ := by
  rw [Fintype.prod_sum_type]
  unfold reducedStarProductLeaves
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    simp only [slotFn, slotTs, argSrc, slotNode, cosetDecoration]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    rw [← parentClockWith_eq_clockOf, ← parentClockWith_eq_clockOf]
  · refine Finset.prod_congr rfl fun b _ => ?_
    simp only [slotFn, slotTs, argSrc, slotNode, cosetDecoration]
    simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
    rw [← parentClockWith_eq_clockOf]
    rfl

/-- The chi constant, as a function of `d`. -/
noncomputable def Cchi (d : ℕ) : ℝ := if h : 1 ≤ d then Classical.choose (exists_Cchi h) else 1

theorem Cchi_spec (hd : 1 ≤ d) : 1 ≤ Cchi d ∧ ∀ H : Mom d → ℂ, ContDiff ℝ (30 * d) H → ∀ n : Fin d → ℤ,
    SNorm (30 * d) 0 (fun k => chiC d n k * H k) ≤ ENNReal.ofReal (Cchi d) * SNorm (30 * d) 0 H := by
  unfold Cchi; simp only [hd, dite_true]; exact Classical.choose_spec (exists_Cchi hd)

end WaveTurbulence.Represents
