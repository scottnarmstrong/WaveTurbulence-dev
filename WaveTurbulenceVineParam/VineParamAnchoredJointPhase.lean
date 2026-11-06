/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamAnchoredPhases
import Mathlib.Tactic

/-! # Preservation of the boundary-corrected included-joint phase

This composition helper consumes an already proved old joint phase.
-/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Reanchoring the physical reference cancels the entire joint translation
correction, giving precisely the original contract joint phase. -/
theorem anchoredInsertionChart_joint_of_old {d : ℕ} {ι : Type*} [DecidableEq ι]
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : Mom d)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → Mom d)) (ref : ι)
    (hphase : ∀ z,directedEnergy G.ends b (old.symm z).1+‖g‖^2-‖g-r‖^2=
      2*inner ℝ r (z ref)) (x : ι ⊕ Fin 2 → Mom d) :
    directedEnergy G.newEnds (.inl b)
      ((G.anchoredInsertionChart a b hab ha hb r old ref (decide (b ∈ G.cap))).symm x).1+
        ‖g‖^2-‖g-r‖^2=2*inner ℝ r (x (.inl ref)) := by
  let z := G.insertionOldCoordinates a b r ref (decide (b ∈ G.cap)) x
  let xy : Mom d×Mom d := (-x (.inr 0),x (.inr 1))
  have he := G.globalSourceChart_energy a b hab ha hb r (old.symm z) xy b
  have hf : directedFlow G.ends b (old.symm z).1=r := by
    simpa only [rootForcing,Ne.symm hab,ite_false,ite_true] using (old.symm z).2 b
  rw [hb,hf] at he
  rw [G.anchoredInsertionChart_decode_labels]
  change directedEnergy G.newEnds (.inl b)
    ((G.globalSourceChart a b hab ha hb r).symm (old.symm z,xy)).1+
      ‖g‖^2-‖g-r‖^2=_
  rw [he]
  have hz := hphase z
  change directedEnergy G.ends b (old.symm z).1+‖g‖^2-‖g-r‖^2=
    2*inner ℝ r (x (.inl ref)-(if ref=ref ∧ decide (b ∈ G.cap)=true then
      G.pattern.correction (spliceGap G.cap a b r) xy else 0)) at hz
  simp only [true_and,decide_eq_true_eq,inner_sub_right] at hz
  linarith

end WaveTurbulence.Vine.Param.RungSpliceGeometry
