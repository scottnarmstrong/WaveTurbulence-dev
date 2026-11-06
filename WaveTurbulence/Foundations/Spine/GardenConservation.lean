/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenSlots
import Mathlib.Tactic

/-!
# Conservation through the actual garden incidence bijection

TARGET `decmole1` and `molecv`: the missing slots give the root boundary
source, and the occupied slots give exactly the actual molecule dart sum.
-/

public section
namespace WaveTurbulence.Mole
open Finset TTree
variable {w : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (G : Garden w)

/-- The signed coefficient of a parent/left/middle/right incidence. -/
@[expose] def slotWeight (v : GBranch G.tree) (i : Fin 4) : ℝ :=
  if G.sign v.toNode = 1 then (if i.val%2 = 0 then 1 else -1)
  else (if i.val%2 = 1 then 1 else -1)

theorem slotWeight_dart (x : GardenDart G) :
    slotWeight G (G.molecule.atom x) (dartPosition G x) = G.molecule.dartSign x := by
  unfold Molecule.dartSign
  rw [dart_out_profile]
  unfold slotWeight
  split <;> simp

/-- Four signed node values, including the boundary slots absent as bonds. -/
@[expose] def slotSum (κ : GNode G.tree → E) (v : GBranch G.tree) : E :=
  ∑ i : Fin 4, slotWeight G v i • κ (slotNode G v i)

/-- Root boundary source, computed by setting every actual bond value to
zero. This includes both branching roots and leaves paired to trivial roots. -/
@[expose] def gardenSource (hP : G.IsPlain) (n : Fin w → E) (v : GBranch G.tree) : E :=
  -slotSum G (extendLabels G hP n (fun _ => 0)) v

/-- The four-slot sum splits into actual bond incidences and the prescribed
root boundary source, with loops counted at both incidences. -/
theorem slotSum_extension (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (hk : ∀ x, k (G.molecule.mate x) = k x) (v : GBranch G.tree) :
    slotSum G (extendLabels G hP n k) v =
      (∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • k x) - gardenSource G hP n v := by
  let f : Fin 4 → E := fun i => slotWeight G v i •
    (extendLabels G hP n k (slotNode G v i) -
      extendLabels G hP n (fun _ => 0) (slotNode G v i))
  let S := (G.molecule.dartsAt v).image (dartPosition G)
  have hinj : Set.InjOn (dartPosition G) (G.molecule.dartsAt v) := by
    intro x hx y hy hxy
    apply atom_position_injective G
    exact Prod.ext (((mem_dartsAt _ _ _).mp hx).trans ((mem_dartsAt _ _ _).mp hy).symm) hxy
  have hsum : ∑ i : Fin 4, f i = ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • k x := by
    calc
      _ = ∑ i ∈ S, f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _hi hnot
        have hmissing : ¬ ∃ x : GardenDart G, G.molecule.atom x = v ∧ dartPosition G x = i := by
          rintro ⟨x,hx,hp⟩
          exact hnot (Finset.mem_image.mpr ⟨x,(mem_dartsAt _ _ _).mpr hx,hp⟩)
        dsimp only [f]
        rw [missing_slot_fixed G hP n k (fun _ => 0) v i hmissing,sub_self,smul_zero]
      _ = ∑ x ∈ G.molecule.dartsAt v, f (dartPosition G x) := Finset.sum_image hinj
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hv := (mem_dartsAt _ _ _).mp hx
        have h1 := congrFun (restrict_extendLabels G hP n k hk) x
        have h0 := congrFun (restrict_extendLabels G hP n (fun _ => (0:E)) (fun _ => rfl)) x
        change extendLabels G hP n k (dartNode G x) = k x at h1
        change extendLabels G hP n (fun _ => (0:E)) (dartNode G x) = 0 at h0
        dsimp only [f]
        rw [← hv,slotNode_dart,slotWeight_dart,h1,h0,sub_zero]
  have hh : ∑ i : Fin 4, f i = slotSum G (extendLabels G hP n k) v + gardenSource G hP n v := by
    dsimp only [f,slotSum,gardenSource]
    rw [← sub_eq_add_neg]
    simp only [smul_sub,Finset.sum_sub_distrib]
  rw [hh] at hsum
  exact eq_sub_iff_add_eq.mpr hsum

/-- The four-slot conservation equation is precisely the ternary-tree
branching relation, with the actual orientation signs. -/
theorem slotSum_eq_zero_iff (κ : GNode G.tree → E) (v : GBranch G.tree) :
    slotSum G κ v = 0 ↔ κ v.toNode = κ (v.child 0) - κ (v.child 1) + κ (v.child 2) := by
  unfold slotSum
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  by_cases hs : G.sign v.toNode = 1
  · simp only [slotWeight,hs,ite_true]
    norm_num
    change κ v.toNode + (-(κ (v.child 0)) + (κ (v.child 1) + -(κ (v.child 2)))) = 0 ↔ _

    constructor
    · intro h
      calc
        κ v.toNode = (κ v.toNode + (-κ (v.child 0) + (κ (v.child 1) + (-κ (v.child 2))))) +
          (κ (v.child 0) - κ (v.child 1) + κ (v.child 2)) := by abel
        _ = _ := by rw [h,zero_add]
    · intro h
      rw [h]
      abel
  · simp only [slotWeight,hs,ite_false]
    norm_num
    change -κ v.toNode + (κ (v.child 0) + (-κ (v.child 1) + κ (v.child 2))) = 0 ↔ _
    constructor
    · intro h
      calc
        κ v.toNode = -(-κ v.toNode + (κ (v.child 0) + (-κ (v.child 1) + κ (v.child 2)))) +
          (κ (v.child 0) - κ (v.child 1) + κ (v.child 2)) := by abel
        _ = _ := by rw [h,neg_zero,zero_add]
    · intro h
      rw [h]
      abel

end WaveTurbulence.Mole
