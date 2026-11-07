/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeCore
public import WaveTurbulence.Foundations.FinalCount.MoleculeCutValidity
import Mathlib.Tactic

/-! # Source beta splits and actual bridge preservation -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Collapsing the fresh split vertex recovers every old dart endpoint. -/
theorem cut_fold_atom (M : Molecule V D) {v w : V} {x y : D}
    (hd : M.IsCutData v w x y) (e : D) :
    (if (M.cut v w x y).atom e = w then v else (M.cut v w x y).atom e) = M.atom e := by
  have hnot : M.atom e ≠ w := fun h => hd.2.1 (h ▸ M.atom_mem e)
  rcases Mole.cut_atom_cases (v := v) (v2 := w) (x1 := x) (x2 := y) M e with h | ⟨h,h'⟩
  · rw [h,ite_eq_right hnot]
  · rw [h',ite_eq_left rfl,h]

/-- A split cannot reconnect the two sides of an old bridge.  The proof
projects an actual avoiding path through the fresh atom onto the old graph. -/
theorem isBridge_cut_of_isBridge (M : Molecule V D) {v w : V} {x y e : D}
    (hd : M.IsCutData v w x y) (he : IsBridge M e) : IsBridge (M.cut v w x y) e := by
  let C := M.cut v w x y
  let f : V → V := fun a => if a = w then v else a
  have hf (z : D) : f (C.atom z) = M.atom z := cut_fold_atom M hd z
  have hmap (a b : V) (hab : AdjWithoutBond C e a b) : AdjWithoutBond M e (f a) (f b) := by
    obtain ⟨z,hza,hzb,hze,hzme⟩ := hab
    refine ⟨z,?_,?_,hze,hzme⟩
    · rw [← hf z,hza]
    · rw [← hf (M.mate z)]
      exact congrArg f hzb
  have hp (a b : V) (hab : Relation.EqvGen (AdjWithoutBond C e) a b) :
      Relation.EqvGen (AdjWithoutBond M e) (f a) (f b) := by
    induction hab with
    | rel a b h => exact Relation.EqvGen.rel _ _ (hmap a b h)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro h
  apply he
  have hh := hp _ _ h
  change Relation.EqvGen (AdjWithoutBond M e) (f (C.atom e)) (f (C.atom (M.mate e))) at hh
  rw [hf e,hf (M.mate e)] at hh
  exact hh

/-- Bridge deletion commutes with a split whose selected darts survive.
This is the literal atom-map identity on the actual surviving dart carrier. -/
theorem numComponents_eraseBond_cut_eq (M : Molecule V D) {v w : V} {x y e : D}
    (hx : x ≠ e ∧ x ≠ M.mate e) (hy : y ≠ e ∧ y ≠ M.mate e) :
    (eraseBond (M.cut v w x y) e).numComponents =
      ((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩).numComponents := by
  classical
  let f : WithoutBondDart (M.cut v w x y) e ≃ WithoutBondDart M e := Equiv.refl _
  refine (numComponents_and_circuitRank_eq_of_dart_equiv
    (eraseBond (M.cut v w x y) e) ((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩)
    f rfl ?_ ?_ (fun _ => rfl)).1
  · intro z
    change (if M.atom z.val = v ∧ z ≠ ⟨x,hx⟩ ∧ z ≠ ⟨y,hy⟩ then w else M.atom z.val) =
      (if M.atom z.val = v ∧ z.val ≠ x ∧ z.val ≠ y then w else M.atom z.val)
    have hzx : (z ≠ ⟨x,hx⟩) ↔ z.val ≠ x :=
      ⟨fun h he => h (Subtype.ext he),fun h he => h (congrArg Subtype.val he)⟩
    have hzy : (z ≠ ⟨y,hy⟩) ↔ z.val ≠ y :=
      ⟨fun h he => h (Subtype.ext he),fun h he => h (congrArg Subtype.val he)⟩
    simp only [hzx,hzy]
  · intro z
    exact Subtype.ext rfl

/-- A source beta split disconnects by exactly the same component increment
before or after deleting an old bridge away from its chosen darts.  Thus B
cannot newly enable that split. -/
theorem cut_component_increment_eraseBond_eq (M : Molecule V D) {v w : V} {x y e : D}
    (hd : M.IsCutData v w x y) (he : IsBridge M e)
    (hx : x ≠ e ∧ x ≠ M.mate e) (hy : y ≠ e ∧ y ≠ M.mate e) :
    (((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩).numComponents : ℤ) -
        (eraseBond M e).numComponents =
      ((M.cut v w x y).numComponents : ℤ) - M.numComponents := by
  have hcut := isBridge_cut_of_isBridge M hd he
  have hF := numComponents_eraseBond_eq_add_one M e he
  have hFC := numComponents_eraseBond_eq_add_one (M.cut v w x y) e hcut
  rw [numComponents_eraseBond_cut_eq M hx hy] at hFC
  omega

/-- An avoiding path after splitting projects to an OLD avoiding path. -/
theorem cut_avoiding_path_projects (M : Molecule V D) {v w : V} {x y e : D}
    (hd : M.IsCutData v w x y) {a b : V}
    (hp : Relation.EqvGen (AdjWithoutBond (M.cut v w x y) e) a b) :
    Relation.EqvGen (AdjWithoutBond M e) (if a = w then v else a) (if b = w then v else b) := by
  let C := M.cut v w x y
  let f : V → V := fun a => if a = w then v else a
  have hf (z : D) : f (C.atom z) = M.atom z := cut_fold_atom M hd z
  have hmap (a b : V) (hab : AdjWithoutBond C e a b) : AdjWithoutBond M e (f a) (f b) := by
    obtain ⟨z,hza,hzb,hze,hzme⟩ := hab
    refine ⟨z,?_,?_,hze,hzme⟩
    · rw [← hf z,hza]
    · rw [← hf (M.mate z)]
      exact congrArg f hzb
  induction hp with
  | rel a b h => exact Relation.EqvGen.rel _ _ (hmap a b h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Deleting an old bridge cannot disconnect the two split joints if they
were connected after the split. Crossing that bridge would project to an
old avoiding cycle because both joints fold onto the same old atom. -/
theorem cut_joints_sameComponent_eraseBond_iff (M : Molecule V D) {v w : V} {x y e : D}
    (hd : M.IsCutData v w x y) (he : IsBridge M e) :
    (M.cut v w x y).SameComponent v w ↔ (eraseBond (M.cut v w x y) e).SameComponent v w := by
  let C := M.cut v w x y
  have hcut := isBridge_cut_of_isBridge M hd he
  have hvw : v ≠ w := (Mole.cut_fresh_ne M hd).symm
  have hf (z : D) := cut_fold_atom M hd z
  have hproj (a b : V) (hp : (eraseBond C e).SameComponent a b) :
      Relation.EqvGen (AdjWithoutBond M e) (if a = w then v else a) (if b = w then v else b) :=
    cut_avoiding_path_projects M hd ((eraseBond_sameComponent_iff C e a b).mp hp)
  constructor
  · intro hp
    rcases (sameComponent_eraseBond_add_edge C e hcut v w).mp hp with hp | ⟨hva,hbw⟩ | ⟨hvb,haw⟩
    · exact hp
    · have h1 := hproj _ _ hva
      have h2 := hproj _ _ hbw
      rw [ite_eq_right hvw,hf e] at h1
      change Relation.EqvGen (AdjWithoutBond M e)
        (if C.atom (M.mate e) = w then v else C.atom (M.mate e)) (if w = w then v else w) at h2
      rw [hf (M.mate e),ite_eq_left rfl] at h2
      exact False.elim (he (Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ h2 h1)))
    · have h1 := hproj _ _ hvb
      have h2 := hproj _ _ haw
      change Relation.EqvGen (AdjWithoutBond M e) (if v = w then v else v)
        (if C.atom (M.mate e) = w then v else C.atom (M.mate e)) at h1
      rw [ite_eq_right hvw,hf (M.mate e)] at h1
      rw [hf e,ite_eq_left rfl] at h2
      exact False.elim (he (Relation.EqvGen.trans _ _ _ h2 h1))
  · intro hp
    exact Relation.EqvGen.mono (fun _ _ ⟨z,hza,hzb⟩ => ⟨z.val,hza,hzb⟩) v w hp

/-- The commuting B/split operations preserve actual paths, not merely F. -/
theorem sameComponent_eraseBond_cut_iff (M : Molecule V D) {v w : V} {x y e : D}
    (hx : x ≠ e ∧ x ≠ M.mate e) (hy : y ≠ e ∧ y ≠ M.mate e) (a b : V) :
    (eraseBond (M.cut v w x y) e).SameComponent a b ↔
      ((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩).SameComponent a b := by
  have hatom (z : WithoutBondDart M e) :
      ((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩).atom z =
      (eraseBond (M.cut v w x y) e).atom z := by
    change (if M.atom z.val = v ∧ z ≠ ⟨x,hx⟩ ∧ z ≠ ⟨y,hy⟩ then w else M.atom z.val) =
      (if M.atom z.val = v ∧ z.val ≠ x ∧ z.val ≠ y then w else M.atom z.val)
    have hzx : (z ≠ ⟨x,hx⟩) ↔ z.val ≠ x :=
      ⟨fun h he => h (Subtype.ext he),fun h he => h (congrArg Subtype.val he)⟩
    have hzy : (z ≠ ⟨y,hy⟩) ↔ z.val ≠ y :=
      ⟨fun h he => h (Subtype.ext he),fun h he => h (congrArg Subtype.val he)⟩
    simp only [hzx,hzy]
  have hadj (c d : V) : (eraseBond (M.cut v w x y) e).Adj c d ↔
      ((eraseBond M e).cut v w ⟨x,hx⟩ ⟨y,hy⟩).Adj c d := by
    constructor
    · rintro ⟨z,hzc,hzd⟩
      exact ⟨z,(hatom z).trans hzc,(hatom ((eraseBond M e).mate z)).trans hzd⟩
    · rintro ⟨z,hzc,hzd⟩
      exact ⟨z,(hatom z).symm.trans hzc,(hatom ((eraseBond M e).mate z)).symm.trans hzd⟩
  exact ⟨Relation.EqvGen.mono (fun c d h => (hadj c d).mp h) a b,
    Relation.EqvGen.mono (fun c d h => (hadj c d).mpr h) a b⟩

end WaveTurbulence.MoleProp
