/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceEnergyTransport
public import WaveTurbulenceVineParam.VineParamJoint
import Mathlib.Tactic

/-! # The physical two-bond joint row from actual source degree counts -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- The actual unique outgoing and incoming internal joint occurrences. -/
structure DirectedJointRow (ends : β → V×V) (v : V) where
  outgoing : β
  incoming : β
  distinct : outgoing ≠ incoming
  outgoing_at : (ends outgoing).1=v
  incoming_at : (ends incoming).2=v
  row : ∀ e,-energySign ends v e=(if e=outgoing then 1 else 0)-(if e=incoming then 1 else 0)

/-- Source degree one in each direction and absence of a joint loop produce
both actual occurrences and the full incidence row before decorations. -/
theorem exists_directedJointRow (ends : β → V×V) (v : V)
    (ho : ((univ : Finset β).filter (fun e => (ends e).1=v)).card=1)
    (hi : ((univ : Finset β).filter (fun e => (ends e).2=v)).card=1)
    (hloop : ∀ e,¬ ((ends e).1=v ∧ (ends e).2=v)) : Nonempty (DirectedJointRow ends v) := by
  obtain ⟨out,hout⟩ := card_eq_one.mp ho
  obtain ⟨inc,hinc⟩ := card_eq_one.mp hi
  have heo : ∀ e,(ends e).1=v ↔ e=out := by
    intro e
    simpa only [mem_filter,mem_univ,true_and,mem_singleton] using (Finset.ext_iff.mp hout e)
  have hei : ∀ e,(ends e).2=v ↔ e=inc := by
    intro e
    simpa only [mem_filter,mem_univ,true_and,mem_singleton] using (Finset.ext_iff.mp hinc e)
  refine ⟨⟨out,inc,?_,(heo out).mpr rfl,(hei inc).mpr rfl,?_⟩⟩
  · intro h
    exact hloop out ⟨(heo out).mpr rfl,(hei out).mpr h⟩
  · intro e
    simp only [energySign,neg_sub,heo e,hei e]

namespace DirectedJointRow
variable {ends : β → V×V} {v : V} (Q : DirectedJointRow ends v)

/-- Actual joint flow is its outgoing label minus its incoming label. -/
theorem flow {E : Type*} [AddCommGroup E] (k : β → E) :
    directedFlow ends v k=k Q.outgoing-k Q.incoming := by
  simp [directedFlow,Q.row,sub_smul]

/-- Negative molecular Gamma at the joint uses exactly its two actual labels. -/
theorem energy {E : Type*} [NormedAddCommGroup E] (k : β → E) :
    directedEnergy ends v k=‖k Q.incoming‖^2-‖k Q.outgoing‖^2 := by
  rw [directedEnergy_eq_neg_flow,Q.flow]
  ring

/-- The complete boundary-corrected joint phase is the exact contract
reference normal form, derived solely from the physical source flow. -/
theorem boundary_phase {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g r : E) (k : β → E) (hflow : directedFlow ends v k=r) :
    directedEnergy ends v k+‖g‖^2-‖g-r‖^2=2*inner ℝ r (g-k Q.outgoing) := by
  rw [Q.flow] at hflow
  have hin : k Q.incoming=k Q.outgoing-r := by rw [← hflow]; abel
  rw [Q.energy,hin]
  have h := joint_resonance g (k Q.outgoing) r
  change ‖g‖^2-‖g-r‖^2-‖k Q.outgoing‖^2+‖k Q.outgoing-r‖^2=
    2*inner ℝ r (g-k Q.outgoing) at h
  linarith only [h]

end DirectedJointRow
end WaveTurbulence.Vine.Param
