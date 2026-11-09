/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Cut algebra for symmetric weights (packet L3)

Generic facts about edge cuts of a finite vertex set `A` with a symmetric, loop-free weight `w : V → V → ℕ`
(for a multigraph: `w u v = mult s(u, v)`):

* `cutW_inter_union_le` (submodularity), `cutW_diff_le` (posimodularity), `cutW_compl` (symmetry);
* `cutW_even` (all degrees even ⇒ every cut even);
* `two_le_cutW` (connected, even ⇒ every nonempty proper side has cut `≥ 2`);
* `connOn_of_cutW_two` (a side of a 2-edge-cut induces a connected subgraph);
* `uncross_diff`, `uncross_inter_union` (two crossing 2-cut sides give 2-cut sides).

These are the inputs of the uncrossing proof of N3 Theorem 6 (research note N3 §1.4; the chain form is this packet's
reading, see HANDOFF.md).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct.CutAlg

open Finset

variable {V : Type*} [DecidableEq V]

/-- The number of weighted pairs `(u, v)` with `u ∈ X`, `v ∈ A ∖ X` (both in `A`). -/
def cutW (w : V → V → ℕ) (A X : Finset V) : ℕ :=
  ∑ u ∈ A, ∑ v ∈ A, if u ∈ X ∧ v ∉ X then w u v else 0

/-- The weighted degree of `u` in `A`. -/
def degW (w : V → V → ℕ) (A : Finset V) (u : V) : ℕ := ∑ v ∈ A, w u v

/-- The weight between two sets. -/
def eW (w : V → V → ℕ) (X Y : Finset V) : ℕ := ∑ u ∈ X, ∑ v ∈ Y, w u v

/-- Adjacency inside `X` (L1's `AdjIn` for `w = mult s(·, ·)`). -/
def AdjW (w : V → V → ℕ) (X : Finset V) (a b : V) : Prop := a ∈ X ∧ b ∈ X ∧ w a b ≠ 0

/-- `X` induces a connected subgraph (L1's `ConnOn`). -/
def ConnW (w : V → V → ℕ) (X : Finset V) : Prop := ∀ u ∈ X, ∀ v ∈ X, Relation.ReflTransGen (AdjW w X) u v

/-- Symmetric weight. -/
def Symm (w : V → V → ℕ) : Prop := ∀ u v, w u v = w v u

theorem cutW_eq_eW (w : V → V → ℕ) {A X : Finset V} (hX : X ⊆ A) : cutW w A X = eW w X (A \ X) := by
  unfold cutW eW
  rw [← Finset.sum_filter_add_sum_filter_not A (· ∈ X)]
  have h1 : ∑ u ∈ A.filter (· ∈ X), ∑ v ∈ A, (if u ∈ X ∧ v ∉ X then w u v else 0) =
      ∑ u ∈ X, ∑ v ∈ A \ X, w u v := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hX]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext v; simp [hu, Finset.mem_sdiff]
  have h2 : ∑ u ∈ A.filter (fun u => ¬ u ∈ X), ∑ v ∈ A, (if u ∈ X ∧ v ∉ X then w u v else 0) = 0 := by
    refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun v _ => ?_
    simp only [Finset.mem_filter] at hu
    simp [hu.2]
  rw [h1, h2, add_zero]

/-- **Submodularity.** -/
theorem cutW_inter_union_le (w : V → V → ℕ) (A X Y : Finset V) :
    cutW w A (X ∩ Y) + cutW w A (X ∪ Y) ≤ cutW w A X + cutW w A Y := by
  unfold cutW
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases hux : u ∈ X <;> by_cases huy : u ∈ Y <;> by_cases hvx : v ∈ X <;> by_cases hvy : v ∈ Y <;>
    simp [hux, huy, hvx, hvy]

/-- **Symmetry**: `δ(X) = δ(A ∖ X)` for a symmetric weight. -/
theorem cutW_compl {w : V → V → ℕ} (hw : Symm w) (A X : Finset V) : cutW w A (A \ X) = cutW w A X := by
  unfold cutW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
  by_cases hux : u ∈ X <;> by_cases hvx : v ∈ X <;> simp [hux, hvx, hu, hv, hw u v]

/-- **Posimodularity.** -/
theorem cutW_diff_le {w : V → V → ℕ} (hw : Symm w) {A X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ A) :
    cutW w A (X \ Y) + cutW w A (Y \ X) ≤ cutW w A X + cutW w A Y := by
  have h := cutW_inter_union_le w A X (A \ Y)
  rw [cutW_compl hw] at h
  have e1 : X ∩ (A \ Y) = X \ Y := by
    ext x; constructor
    · intro hx; simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢; exact ⟨hx.1, hx.2.2⟩
    · intro hx; simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢; exact ⟨hx.1, hX hx.1, hx.2⟩
  have e2 : cutW w A (X ∪ (A \ Y)) = cutW w A (Y \ X) := by
    rw [← cutW_compl hw A (X ∪ (A \ Y))]
    congr 1
    ext x; constructor
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or, not_and, not_not] at hx ⊢
      exact ⟨hx.2.2 hx.1, hx.2.1⟩
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or, not_and, not_not] at hx ⊢
      exact ⟨hY hx.1, hx.2, fun _ => hx.1⟩
  rw [e1, e2] at h
  exact h

/-- The cut of a disjoint union, minus twice the weight between the parts. -/
theorem cutW_union_disjoint {w : V → V → ℕ} (hw : Symm w) {A X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ A)
    (hXY : Disjoint X Y) : cutW w A (X ∪ Y) + 2 * eW w X Y = cutW w A X + cutW w A Y := by
  rw [cutW_eq_eW w hX, cutW_eq_eW w hY, cutW_eq_eW w (Finset.union_subset hX hY)]
  unfold eW
  rw [Finset.sum_union hXY]
  have hAX : A \ X = (A \ (X ∪ Y)) ∪ Y := by
    ext x; constructor
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢; tauto
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
      rcases hx with ⟨h1, h2, h3⟩ | h
      · exact ⟨h1, h2⟩
      · exact ⟨hY h, Finset.disjoint_right.mp hXY h⟩
  have hAY : A \ Y = (A \ (X ∪ Y)) ∪ X := by
    ext x; constructor
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢; tauto
    · intro hx; simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hx ⊢
      rcases hx with ⟨h1, h2, h3⟩ | h
      · exact ⟨h1, h3⟩
      · exact ⟨hX h, Finset.disjoint_left.mp hXY h⟩
  have d1 : Disjoint (A \ (X ∪ Y)) Y := by
    rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto
  have d2 : Disjoint (A \ (X ∪ Y)) X := by
    rw [Finset.disjoint_left]; intro x hx hy; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto
  have hsym : ∑ u ∈ Y, ∑ v ∈ X, w u v = ∑ u ∈ X, ∑ v ∈ Y, w u v := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hw v u
  rw [hAX, hAY]
  simp only [Finset.sum_union d1, Finset.sum_union d2, Finset.sum_add_distrib]
  rw [hsym]; ring

/-- A loop-free weight. -/
def Loopless (w : V → V → ℕ) : Prop := ∀ u, w u u = 0

/-- The weight inside a set is even (each pair counted twice). -/
theorem even_eW_self {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) (X : Finset V) : Even (eW w X X) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  unfold eW
  rw [← Finset.sum_product']
  push_cast
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    rw [hw p.1 p.2]
    have : ((w p.2 p.1 : ℕ) : ZMod 2) + (w p.2 p.1 : ZMod 2) = 2 * (w p.2 p.1 : ZMod 2) := by ring
    simp only [this]
    exact mul_eq_zero_of_left (by decide) _
  · intro p _ hne heq
    apply hne
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq] at heq
    rw [heq.1, hl] ; simp
  · intro p hp; simpa [Finset.mem_product, and_comm] using hp
  · intro p _; rfl

/-- **Parity**: if every degree in `A` is even, every cut is even. -/
theorem cutW_even {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) {A X : Finset V} (hX : X ⊆ A)
    (hdeg : ∀ u ∈ A, Even (degW w A u)) : Even (cutW w A X) := by
  have hsplit : ∑ u ∈ X, degW w A u = eW w X X + cutW w A X := by
    rw [cutW_eq_eW w hX]
    unfold degW eW
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hX]
  have hsum : Even (∑ u ∈ X, degW w A u) := Finset.even_sum _ fun u hu => hdeg u (hX hu)
  rw [hsplit] at hsum
  exact (Nat.even_add.mp hsum).mp (even_eW_self hw hl X)

/-- Connectedness of `A` gives a positive cut for every nonempty proper side. -/
theorem cutW_pos {w : V → V → ℕ} {A X : Finset V} (hX : X ⊆ A) (hconn : ConnW w A) {u v : V} (hu : u ∈ X)
    (hv : v ∈ A) (hvX : v ∉ X) : 0 < cutW w A X := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hzero : ∀ a ∈ X, ∀ b ∈ A, b ∉ X → w a b = 0 := by
    intro a ha b hb hbX
    rw [cutW_eq_eW w hX] at h0
    unfold eW at h0
    have h1 := (Finset.sum_eq_zero_iff.mp h0) a ha
    exact (Finset.sum_eq_zero_iff.mp h1) b (Finset.mem_sdiff.mpr ⟨hb, hbX⟩)
  have key : ∀ b, Relation.ReflTransGen (AdjW w A) u b → b ∈ X := by
    intro b hb
    induction hb with
    | refl => exact hu
    | @tail b' c' _ hbc ih =>
      by_contra hc
      exact hbc.2.2 (hzero b' ih c' hbc.2.1 hc)
  exact hvX (key v (hconn u (hX hu) v hv))

/-- **Lower bound**: in a connected `A` with even degrees, every nonempty proper side has cut `≥ 2`. -/
theorem two_le_cutW {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) {A X : Finset V} (hX : X ⊆ A)
    (hconn : ConnW w A) (hdeg : ∀ u ∈ A, Even (degW w A u)) {u v : V} (hu : u ∈ X) (hv : v ∈ A) (hvX : v ∉ X) :
    2 ≤ cutW w A X := by
  have hp := cutW_pos hX hconn hu hv hvX
  obtain ⟨k, hk⟩ := cutW_even hw hl hX hdeg
  omega

/-- The vertices of `X` reachable from `u` inside `X`. -/
noncomputable def reach (w : V → V → ℕ) (X : Finset V) (u : V) : Finset V := by
  classical
  exact X.filter fun b => Relation.ReflTransGen (AdjW w X) u b

theorem mem_reach {w : V → V → ℕ} {X : Finset V} {u b : V} :
    b ∈ reach w X u ↔ b ∈ X ∧ Relation.ReflTransGen (AdjW w X) u b := by
  classical
  unfold reach; simp only [Finset.mem_filter]

/-- No weight leaves the reachable set inside `X`. -/
theorem eW_reach_zero {w : V → V → ℕ} {X : Finset V} (u : V) :
    eW w (reach w X u) (X \ reach w X u) = 0 := by
  unfold eW
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  rw [mem_reach] at ha
  rw [Finset.mem_sdiff, mem_reach] at hb
  by_contra hne
  exact hb.2 ⟨hb.1, ha.2.tail ⟨ha.1, hb.1, hne⟩⟩

/-- **A side of a 2-edge-cut is connected** (in a connected `A` with even degrees). -/
theorem connW_of_cutW_two {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) {A X : Finset V} (hX : X ⊆ A)
    (hconn : ConnW w A) (hdeg : ∀ u ∈ A, Even (degW w A u)) (h2 : cutW w A X = 2) : ConnW w X := by
  classical
  intro u hu v hv
  by_contra hnot
  set P := reach w X u with hP
  have hPX : P ⊆ X := fun b hb => (mem_reach.mp hb).1
  have huP : u ∈ P := mem_reach.mpr ⟨hu, Relation.ReflTransGen.refl⟩
  have hvP : v ∉ P := fun h => hnot (mem_reach.mp h).2
  set Q := X \ P with hQ
  have hQX : Q ⊆ X := Finset.sdiff_subset
  have hvQ : v ∈ Q := Finset.mem_sdiff.mpr ⟨hv, hvP⟩
  have hdisj : Disjoint P Q := Finset.disjoint_sdiff
  have hunion : P ∪ Q = X := Finset.union_sdiff_of_subset hPX
  have he : eW w P Q = 0 := eW_reach_zero u
  have hcut := cutW_union_disjoint hw (hPX.trans hX) (hQX.trans hX) hdisj
  rw [hunion, he, h2] at hcut
  -- both parts have a vertex outside them in `A`
  have hP2 : 2 ≤ cutW w A P := two_le_cutW hw hl (hPX.trans hX) hconn hdeg huP (hX hv) hvP
  have hQ2 : 2 ≤ cutW w A Q := two_le_cutW hw hl (hQX.trans hX) hconn hdeg hvQ (hX hu)
    (fun h => (Finset.mem_sdiff.mp h).2 huP)
  omega

/-- **Uncrossing, differences.** Two 2-cut sides `X, Y` with `X ∖ Y`, `Y ∖ X` nonempty: both differences are 2-cut
sides. -/
theorem uncross_diff {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) {A X Y : Finset V} (hX : X ⊆ A)
    (hY : Y ⊆ A) (hconn : ConnW w A) (hdeg : ∀ u ∈ A, Even (degW w A u)) (hX2 : cutW w A X = 2)
    (hY2 : cutW w A Y = 2) {a b : V} (ha : a ∈ X) (haY : a ∉ Y) (hb : b ∈ Y) (hbX : b ∉ X) :
    cutW w A (X \ Y) = 2 ∧ cutW w A (Y \ X) = 2 := by
  have h := cutW_diff_le hw hX hY
  have h1 : 2 ≤ cutW w A (X \ Y) :=
    two_le_cutW hw hl (Finset.sdiff_subset.trans hX) hconn hdeg (Finset.mem_sdiff.mpr ⟨ha, haY⟩) (hY hb)
      (fun h => (Finset.mem_sdiff.mp h).2 hb)
  have h2 : 2 ≤ cutW w A (Y \ X) :=
    two_le_cutW hw hl (Finset.sdiff_subset.trans hY) hconn hdeg (Finset.mem_sdiff.mpr ⟨hb, hbX⟩) (hX ha)
      (fun h => (Finset.mem_sdiff.mp h).2 ha)
  omega

/-- **Uncrossing, intersection and union.** Two 2-cut sides `X, Y` with `X ∩ Y` nonempty and `X ∪ Y ≠ A`: both are
2-cut sides. -/
theorem uncross_inter_union {w : V → V → ℕ} (hw : Symm w) (hl : Loopless w) {A X Y : Finset V} (hX : X ⊆ A)
    (hY : Y ⊆ A) (hconn : ConnW w A) (hdeg : ∀ u ∈ A, Even (degW w A u)) (hX2 : cutW w A X = 2)
    (hY2 : cutW w A Y = 2) {a b : V} (ha : a ∈ X ∩ Y) (hb : b ∈ A) (hbXY : b ∉ X ∪ Y) :
    cutW w A (X ∩ Y) = 2 ∧ cutW w A (X ∪ Y) = 2 := by
  have h := cutW_inter_union_le w A X Y
  have h1 : 2 ≤ cutW w A (X ∩ Y) :=
    two_le_cutW hw hl (Finset.inter_subset_left.trans hX) hconn hdeg ha hb
      (fun h => hbXY (Finset.mem_union_left _ (Finset.mem_inter.mp h).1))
  have h2 : 2 ≤ cutW w A (X ∪ Y) :=
    two_le_cutW hw hl (Finset.union_subset hX hY) hconn hdeg (Finset.mem_union_left _ (Finset.mem_inter.mp ha).1)
      hb hbXY
  omega

end WaveTurbulence.TVine.Struct.CutAlg
