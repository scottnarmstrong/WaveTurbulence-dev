/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCapSideAdmissible
import Mathlib.Tactic

/-! # Transporting fixed actual-label differences through a source insertion

These are composition lemmas. An old source producer must prove the old
coordinate difference and geometric cap support before invoking them.
-/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- Every nonreference difference supported on one cap side remains a fixed
difference of actual new bonds, including differences using marked cut bonds. -/
theorem anchoredInsertionChart_difference_old
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref i : ι) (hir : i ≠ ref)
    (anchorInside : Bool) (e f : β) (side : Bool)
    (he : G.AdmissibleSide e side) (hf : G.AdmissibleSide f side)
    (hdiff : ∀ k,old k i=k.1 e-k.1 f) (x : ι ⊕ Fin 2 → E) :
    x (.inl i)=
      ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1 (G.representative e side)-
      ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1 (G.representative f side) := by
  let z := G.insertionOldCoordinates a b r ref anchorInside x
  let xy := (-x (.inr 0),x (.inr 1))
  have hz : z i=x (.inl i) := by simp [z,insertionOldCoordinates,hir]
  have hd := hdiff (old.symm z)
  rw [Equiv.apply_symm_apply,hz] at hd
  rw [G.anchoredInsertionChart_decode_labels]
  exact hd.trans (G.representative_difference a b hab ha hb r (old.symm z) xy e f side he hf)

/-- The physical reference difference g-k is retained by the same exact
reanchoring, using the representative on the included-joint side. -/
theorem anchoredInsertionChart_difference_reference
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (e : β)
    (he : G.AdmissibleSide e (decide (b ∈ G.cap)))
    (hdiff : ∀ k,old k ref=g-k.1 e) (x : ι ⊕ Fin 2 → E) :
    x (.inl ref)=g-
      ((G.anchoredInsertionChart a b hab ha hb r old ref (decide (b ∈ G.cap))).symm x).1
        (G.representative e (decide (b ∈ G.cap))) := by
  let z := G.insertionOldCoordinates a b r ref (decide (b ∈ G.cap)) x
  let xy := (-x (.inr 0),x (.inr 1))
  have hd := hdiff (old.symm z)
  rw [Equiv.apply_symm_apply] at hd
  have hr := G.representative_label a b hab ha hb r (old.symm z) xy e (decide (b ∈ G.cap)) he
  rw [hr] at hd
  rw [G.anchoredInsertionChart_decode_labels]
  change x (.inl ref)-(if ref=ref ∧ decide (b ∈ G.cap)=true then
    G.pattern.correction (spliceGap G.cap a b r) xy else 0)=_ at hd
  simp only [true_and] at hd
  let t := if decide (b ∈ G.cap) then G.pattern.correction (spliceGap G.cap a b r) xy else 0
  calc
    x (.inl ref)=(x (.inl ref)-t)+t := (sub_add_cancel _ _).symm
    _=(g-(((G.globalSourceChart a b hab ha hb r).symm (old.symm z,xy)).1
        (G.representative e (decide (b ∈ G.cap)))+t))+t := congrArg (fun w => w+t) hd
    _=_ := by abel

end WaveTurbulence.Vine.Param.RungSpliceGeometry
