/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2M
public import WaveTurbulence.Foundations.Stage1.Represents.RepRep2
public import WaveTurbulence.Foundations.Stage1.Represents.RepMom2
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D: the slot mode family of a moment-carrying `SlotRepM`

`exists_famM`: the slot family `SlotFam` of a `SlotRepM θ` (unit amplitudes, centres at pairs) with the superposition
identity on the slot boxes and the weighted moments `Σ_l ⟨m_l/2⟩^θ w_l ≤ μ_s` (ready for `tsum_modes_moment`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open scoped ENNReal

variable {w d : ℕ}

open scoped Classical in
theorem exists_famM {θ : ℝ} {S : Garden w} {hS : S.IsPlain} {layer0 : GBranch S.tree → ℕ} {tt : Fin w → ℝ}
    (R : SlotRepM θ S hS d layer0 tt) :
    ∃ fam : SlotFam S d, (∀ s, ∀ ts ∈ R.Box s, ∀ k, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l k *
      fsPhase (fam.m s l) ts) (R.Fn s ts k)) ∧
      ∀ s, ∑' l, maxBracketPow θ (half (fam.m s l)) * ENNReal.ofReal (fam.w s l) ≤ R.μ s := by
  choose Λc cntc wc mc nc ac hc1 hc2 hc3 hc4 hc5 hc6 using R.cp
  choose Λt cntt wt mt at' ht1 ht2 ht3 ht4 ht5 using R.tr
  let fam : SlotFam S d :=
    { Λ := fun s => match s with | Sum.inl p => Λc p | Sum.inr b => Λt b
      cnt := fun s => by cases s with | inl p => exact cntc p | inr b => exact cntt b
      w := fun s => match s with | Sum.inl p => wc p | Sum.inr b => wt b
      m := fun s => match s with | Sum.inl p => mc p | Sum.inr b => mt b
      n := fun s => match s with | Sum.inl p => nc p | Sum.inr b => fun _ _ => 0
      a := fun s => match s with | Sum.inl p => ac p | Sum.inr b => at' b
      w_nn := fun s => by cases s with | inl p => exact hc1 p | inr b => exact ht1 b
      w_sum := fun s => by cases s with | inl p => exact hc2 p | inr b => exact ht2 b
      a_one := fun s l k => by
        cases s with
        | inl p => exact snorm_le_one_pointwise _ _ (hc3 p l) k
        | inr b => exact snorm_le_one_pointwise _ _ (ht3 b l) k
      a_snorm := fun s => by cases s with | inl p => exact hc3 p | inr b => exact ht3 b
      a_supp := fun p l k => hc4 p l k }
  refine ⟨fam, ?_, ?_⟩
  · intro s ts hts k
    cases s with
    | inl p => exact hc5 p ts hts k
    | inr b => exact ht4 b ts hts k
  · intro s
    cases s with
    | inl p => exact hc6 p
    | inr b => exact ht5 b

end WaveTurbulence.Represents
