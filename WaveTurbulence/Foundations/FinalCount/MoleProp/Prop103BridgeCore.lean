/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeComponents
import Mathlib.Tactic

/-! # The actual bridge-free core, obtained by finite source B operations -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The bridge property is a property of the undirected bond, not its chosen dart. -/
theorem isBridge_mate_iff (M : Molecule V D) (e : D) : IsBridge M (M.mate e) ↔ IsBridge M e := by
  have hRel : AdjWithoutBond M (M.mate e) = AdjWithoutBond M e := by
    funext a b
    apply propext
    simp only [AdjWithoutBond,M.mate_mate]
    constructor <;> rintro ⟨x,hx,hxm,h1,h2⟩ <;> exact ⟨x,hx,hxm,h2,h1⟩
  unfold IsBridge
  rw [hRel,M.mate_mate]
  constructor
  · intro h hp
    exact h (Relation.EqvGen.symm _ _ hp)
  · intro h hp
    exact h (Relation.EqvGen.symm _ _ hp)

/-- Actual dart relabeling also preserves the bridge predicate. -/
theorem isBridge_dart_equiv_iff {E : Type v} [Fintype E] [DecidableEq E]
    (M : Molecule V D) (N : Molecule V E) (f : D ≃ E)
    (ha : ∀ x, N.atom (f x) = M.atom x) (hm : ∀ x, N.mate (f x) = f (M.mate x)) (e : D) :
    IsBridge N (f e) ↔ IsBridge M e := by
  have hRel (a b : V) : AdjWithoutBond N (f e) a b ↔ AdjWithoutBond M e a b := by
    constructor
    · rintro ⟨y,hy,hym,hyf,hyfm⟩
      obtain ⟨x,rfl⟩ := f.surjective y
      rw [ha] at hy
      rw [hm,ha] at hym
      refine ⟨x,hy,hym,?_,?_⟩
      · intro h; exact hyf (congrArg f h)
      · intro h; exact hyfm ((congrArg f h).trans (hm e).symm)
    · rintro ⟨x,hx,hxm,hxe,hxme⟩
      refine ⟨f x,(ha x).trans hx,?_,?_,?_⟩
      · rw [hm,ha]; exact hxm
      · intro h; exact hxe (f.injective h)
      · intro h
        rw [hm] at h
        exact hxme (f.injective h)
  have hPath (a b : V) : Relation.EqvGen (AdjWithoutBond N (f e)) a b ↔
      Relation.EqvGen (AdjWithoutBond M e) a b :=
    ⟨fun h => Relation.EqvGen.mono (fun a b h => (hRel a b).mp h) a b h,
      fun h => Relation.EqvGen.mono (fun a b h => (hRel a b).mpr h) a b h⟩
  unfold IsBridge
  rw [ha e,hm e,ha (M.mate e)]
  exact not_congr (hPath _ _)

/-- Both darts of precisely the nonbridge bonds survive all source B operations. -/
abbrev NonBridgeDart (M : Molecule V D) := {x : D // ¬ IsBridge M x}

noncomputable instance nonBridgeDartFintype (M : Molecule V D) : Fintype (NonBridgeDart M) :=
  Fintype.ofFinite _

/-- Remove all old bridge bonds while keeping every old atom, including isolates. -/
def bridgeCore (M : Molecule V D) : Molecule V (NonBridgeDart M) where
  atoms := M.atoms
  atom x := M.atom x.val
  mate x := ⟨M.mate x.val,fun h => x.property ((isBridge_mate_iff M x.val).mp h)⟩
  out x := M.out x.val
  atom_mem x := M.atom_mem x.val
  mate_mate x := Subtype.ext (M.mate_mate x.val)
  mate_ne x h := M.mate_ne x.val (congrArg Subtype.val h)
  out_mate x := M.out_mate x.val

/-- In the bridge-free case the core is exactly the old dart carrier. -/
def bridgeCoreEquivOfNoBridges (M : Molecule V D) (hn : ∀ x, ¬ IsBridge M x) : NonBridgeDart M ≃ D where
  toFun x := x.val
  invFun x := ⟨x,hn x⟩
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl

/-- Deleting one bridge leaves exactly the same final nonbridge core,
with its actual dart carrier identified by a literal subtype flattening. -/
def bridgeCoreEraseEquiv (M : Molecule V D) (e : D) (he : IsBridge M e) :
    NonBridgeDart M ≃ NonBridgeDart (eraseBond M e) where
  toFun x := by
    have hxe : x.val ≠ e := fun h => x.property (h.symm ▸ he)
    have hxme : x.val ≠ M.mate e := fun h =>
      x.property (h.symm ▸ (isBridge_mate_iff M e).mpr he)
    let y : WithoutBondDart M e := ⟨x.val,hxe,hxme⟩
    exact ⟨y,fun h => x.property ((isBridge_eraseBond_iff M e he y).mp h)⟩
  invFun y := ⟨y.val.val,fun h => y.property ((isBridge_eraseBond_iff M e he y.val).mpr h)⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)

/-- The literal core is bridge-free and has exactly the old circuit rank.
The proof performs actual bridge deletions and decreases the actual edge
count; no pruning certificate or eventual-core hypothesis is assumed. -/
theorem bridgeCore_bridgefree_and_circuitRank (M : Molecule V D) :
    (∀ x : NonBridgeDart M, ¬ IsBridge (bridgeCore M) x) ∧ (bridgeCore M).circuitRank = M.circuitRank := by
  classical
  have aux : ∀ n : ℕ, ∀ {E : Type v} [Fintype E] [DecidableEq E] (N : Molecule V E),
      N.bonds.card = n → (∀ x : NonBridgeDart N, ¬ IsBridge (bridgeCore N) x) ∧
        (bridgeCore N).circuitRank = N.circuitRank := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro E _ _ N hn
      by_cases hno : ∀ x : E, ¬ IsBridge N x
      · let f := bridgeCoreEquivOfNoBridges N hno
        constructor
        · intro x hx
          have hh := (isBridge_dart_equiv_iff (bridgeCore N) N f (fun _ => rfl) (fun _ => rfl) x).mpr hx
          exact hno (f x) hh
        · exact circuitRank_eq_of_dart_equiv (bridgeCore N) N f rfl
            (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · push Not at hno
        obtain ⟨e,he⟩ := hno
        have hlt : (eraseBond N e).bonds.card < n := by
          have hh := card_bonds_eraseBond_add_one N e
          omega
        have hrec := ih _ hlt (eraseBond N e) rfl
        let f := bridgeCoreEraseEquiv N e he
        have ha : ∀ x, (bridgeCore (eraseBond N e)).atom (f x) = (bridgeCore N).atom x := fun _ => rfl
        have hm : ∀ x, (bridgeCore (eraseBond N e)).mate (f x) = f ((bridgeCore N).mate x) :=
          fun _ => Subtype.ext (Subtype.ext rfl)
        constructor
        · intro x hx
          exact hrec.1 (f x) ((isBridge_dart_equiv_iff (bridgeCore N) (bridgeCore (eraseBond N e)) f ha hm x).mpr hx)
        · calc
            (bridgeCore N).circuitRank = (bridgeCore (eraseBond N e)).circuitRank :=
              circuitRank_eq_of_dart_equiv _ _ f rfl ha hm (fun _ => rfl)
            _ = (eraseBond N e).circuitRank := hrec.2
            _ = N.circuitRank := circuitRank_eraseBond_eq N e he
  exact aux _ M rfl

/-- Exact local degree loss in the all-bridges removal operation. -/
theorem degree_bridgeCore_add_incident_bridges (M : Molecule V D) (a : V)
    [DecidablePred (IsBridge M)] :
    (bridgeCore M).deg a + ((M.dartsAt a).filter (fun x => IsBridge M x)).card = M.deg a := by
  classical
  have hc : (bridgeCore M).deg a = ((M.dartsAt a).filter (fun x => ¬ IsBridge M x)).card := by
    change ((bridgeCore M).dartsAt a).card = _
    apply card_bij (fun x _ => x.val)
    · intro x hx
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a x.val).mpr ((mem_filter.mp hx).2),x.property⟩
    · intro x _ y _ h
      exact Subtype.ext h
    · intro x hx
      obtain ⟨hx,hnb⟩ := mem_filter.mp hx
      exact ⟨⟨x,hnb⟩,(Mole.mem_dartsAt (bridgeCore M) a _).mpr ((Mole.mem_dartsAt M a x).mp hx),rfl⟩
  rw [hc]
  have hh := card_filter_add_card_filter_not (s := M.dartsAt a) (fun x => IsBridge M x)
  change _ = (M.dartsAt a).card
  omega

end WaveTurbulence.MoleProp
