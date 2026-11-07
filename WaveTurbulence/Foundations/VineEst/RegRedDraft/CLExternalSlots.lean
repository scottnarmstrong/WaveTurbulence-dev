/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLRegionData
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.SlotBoundarySum

/-! # The four actual exterior incidence slots of a CL block -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Finset

variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (D : CLRegionData G S a b)
variable {E : Type*} [AddCommGroup E] [Module ℝ E] (A : GNode G.tree → E)

include hB

theorem cl_externalPositions_upper :
    Finset.univ.filter (fun i => i ∉ Mole.internalPositions G S a) = {0,D.excluded.succ} := by
  classical
  have hv := hB.2.1
  have h0 : (0 : Fin 4) ∉ Mole.internalPositions G S a :=
    fun h => D.parentPattern.1 ((Mole.zero_mem_internalPositions G hv).mp h)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,h0,not_false_eq_true,
      Finset.mem_insert,Finset.mem_singleton,true_or]
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,D.upper,Finset.mem_insert,
      Finset.mem_singleton,Fin.succ_ne_zero,false_or,Fin.succ_inj,not_not]

theorem cl_externalPositions_lower :
    Finset.univ.filter (fun i => i ∉ Mole.internalPositions G S b) = {D.positive.succ,D.negative.succ} := by
  classical
  have hv := hB.2.2.1
  have h0 := (Mole.zero_mem_internalPositions G hv).mpr D.parentPattern.2
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,h0,not_true_eq_false,
      Finset.mem_insert,Finset.mem_singleton,Ne.symm (Fin.succ_ne_zero D.positive),Ne.symm (Fin.succ_ne_zero D.negative),or_self]
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and,D.lower,Finset.mem_insert,
      Finset.mem_singleton,Fin.succ_inj]
    exact D.lower_excluded j

theorem cl_externalSlotSum_upper : externalSlotSum G S A a =
    Mole.slotWeight G a 0 • A a.toNode + Mole.slotWeight G a D.excluded.succ • A (a.child D.excluded) := by
  classical
  unfold externalSlotSum
  rw [cl_externalPositions_upper hB D,Finset.sum_pair (Ne.symm (Fin.succ_ne_zero D.excluded))]
  rfl

theorem cl_externalSlotSum_lower : externalSlotSum G S A b =
    Mole.slotWeight G b D.positive.succ • A (b.child D.positive) +
      Mole.slotWeight G b D.negative.succ • A (b.child D.negative) := by
  classical
  unfold externalSlotSum
  rw [cl_externalPositions_lower hB D,Finset.sum_pair (fun h => D.distinct (Fin.succ_injective _ h))]
  rfl

theorem cl_externalSlotSum_interior (v : GBranch G.tree) (hv : v ∈ S) (ha : v ≠ a) (hb : v ≠ b) :
    externalSlotSum G S A v = 0 := by
  classical
  have hd := hB.2.2.2.2.2.2.2.2.1 v hv ha hb
  have he : Mole.internalPositions G S v = Finset.univ :=
    Finset.eq_univ_of_card _ ((Mole.card_internalPositions G S v).trans hd)
  unfold externalSlotSum
  simp only [he,Finset.mem_univ,not_true_eq_false,Finset.filter_false,Finset.sum_empty]

theorem cl_sum_externalSlotSum : (∑ v ∈ S, externalSlotSum G S A v) =
    externalSlotSum G S A a + externalSlotSum G S A b := by
  classical
  have hdeg := hB
  have hsub : ({a,b} : Finset (GBranch G.tree)) ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hdeg.2.1
    · exact (Finset.mem_singleton.mp hv) ▸ hdeg.2.2.1
  have he : (∑ v ∈ ({a,b} : Finset (GBranch G.tree)), externalSlotSum G S A v) =
      ∑ v ∈ S, externalSlotSum G S A v := by
    apply Finset.sum_subset hsub
    intro v hv hn
    have hne : v ≠ a ∧ v ≠ b := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hn
    exact cl_externalSlotSum_interior hB A v hv hne.1 hne.2
  exact he.symm.trans (Finset.sum_pair hdeg.2.2.2.1)

end WaveTurbulence.RegRed
