/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the assembled weights and the pointwise identity of the skeleton integrand
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ} {S : Garden w}

theorem latticePoint_sub_add (L : ℝ) (a b c : Fin d → ℤ) :
    latticePoint L (a - b + c) = latticePoint L a - latticePoint L b + latticePoint L c := by
  ext j
  simp only [latticePoint, PiLp.add_apply, PiLp.sub_apply, Pi.add_apply, Pi.sub_apply, Int.cast_add,
    Int.cast_sub, add_div, sub_div]

open scoped Classical in
/-- The constant (decoration-independent) part of the weight of the assembled mode. -/
noncomputable def constW (fam : SlotFam S d) (hS : S.IsPlain) (Cχ L : ℝ) (base : Mom d)
    (roots : Fin w → Fin d → ℤ) (tt : Fin w → ℝ) (ξ : XiT fam) : ℂ :=
  (Cχ : ℂ) ^ (Fintype.card (GBranch S.tree)) * (∏ s, ((fam.w s (ξ.1 s) : ℝ) : ℂ)) *
    (if ξ.2 ∈ nodeCentreSet (fam.leafCentre hS ξ.1) then 1 else 0) *
    (∏ s ∈ (Finset.univ : Finset (ReplacementSlot S)).filter (fun s => ¬ hasBond hS s),
      ampS fam Cχ ξ s (base + latticePoint L (kconstInt hS roots s))) *
    ∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)

/-- The edge amplitude of a dart (that of its slot). -/
noncomputable def edgeS (fam : SlotFam S d) (hS : S.IsPlain) (Cχ : ℝ) (ξ : XiT fam) (x : GardenDart S) :
    Mom d → ℂ := ampS fam Cχ ξ (slotOfDart hS x)

/-- The time frequency at a branch. -/
noncomputable def freqS (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (u : GBranch S.tree) : ℝ :=
  modeFreq fam hS ξ (Sum.inr u)

/-- The time dependence of the modes: the product of `e^{πi f_u τ_u}`. -/
noncomputable def timeFac (fam : SlotFam S d) (hS : S.IsPlain) (ξ : XiT fam) (τ : GBranch S.tree → ℝ) : ℂ :=
  ∏ u : GBranch S.tree, Complex.exp (((Real.pi * freqS fam hS ξ u * τ u : ℝ) : ℂ) * Complex.I)

/-- The time arguments of the slot kernels. -/
def slotTs (hS : S.IsPlain) (tt : Fin w → ℝ) (τ : GBranch S.tree → ℝ) (s : ReplacementSlot S) :
    Fin 2 → ℝ := fun i => clockOf S tt τ (argSrc hS s i)

theorem prod_fsPhase_slotTs (fam : SlotFam S d) (hS : S.IsPlain) (tt : Fin w → ℝ)
    (τ : GBranch S.tree → ℝ) (ξ : XiT fam) :
    ∏ s, fsPhase (fam.m s (ξ.1 s)) (slotTs hS tt τ s) =
      (∏ j : Fin w, Complex.exp (((Real.pi * modeFreq fam hS ξ (Sum.inl j) * tt j : ℝ) : ℂ) * Complex.I)) *
        timeFac fam hS ξ τ := by
  classical
  have := prod_slot_phase (fun s => fam.m s (ξ.1 s)) (argSrc hS) (clockOf S tt τ)
  show ∏ s, fsPhase (fam.m s (ξ.1 s)) (fun i => clockOf S tt τ (argSrc hS s i)) = _
  rw [this, Fintype.prod_sum_type]
  rfl

end WaveTurbulence.Represents
