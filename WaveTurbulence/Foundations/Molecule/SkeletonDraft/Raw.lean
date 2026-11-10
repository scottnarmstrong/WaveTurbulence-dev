/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs
public import WaveTurbulence.Foundations.Molecule.DominantChains

/-! # Literal forest and oriented-pair data for the source skeleton operations

DH21 Definition 4.12 and DH21-2 Definition 4.3. Unlike `RawCpl`, these
addresses allow arbitrary width and retain the original root signature.
The pair set forgets only the irrelevant enumeration of oriented leaf pairs.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

abbrev Address (w : ℕ) := Fin w × Path
abbrev Pair (w : ℕ) := Address w × Address w

/-- Literal ordered forest, root signs, and oriented leaf pairs. -/
structure Raw (w : ℕ) where
  sig : Fin w → ℤˣ
  tree : Fin w → TTree
  pairs : Finset (Pair w)

/-- Exact endpoint transport under a source B insertion. -/
def relocate {w : ℕ} (a : Address w) (c l : Fin 3) (z : Address w) : Address w :=
  if z.1 = a.1 ∧ a.2 <+: z.2 then (z.1,a.2 ++ [c,l] ++ z.2.drop a.2.length) else z

/-- Orient a source pair by the sign of its first endpoint. -/
def orient {w : ℕ} (x : Address w) (ζ : ℤˣ) (y : Address w) : Pair w :=
  if ζ = 1 then (x,y) else (y,x)

/-- Source A insertion at a positive/negative leaf pair, with the B2 mini-couple code. -/
def Raw.opA {w : ℕ} (R : Raw w) (x y : Address w) (c : MiniCplCode) : Raw w :=
  let t := TTree.node .leaf .leaf .leaf
  let f := Function.update R.tree x.1 ((R.tree x.1).setAt x.2 t)
  ⟨R.sig,Function.update f y.1 ((f y.1).setAt y.2 t),
    R.pairs.erase (x,y) ∪
      {(addrExt x [0],addrExt y [c.partner 0]),
       (addrExt y [1],addrExt x [1]),
       (addrExt x [2],addrExt y [c.partner 2])}⟩

/-- The two new side pairs of a B insertion, with the pinned six-code table. -/
def miniPairs {w : ℕ} (σ : Fin w → ℤˣ) (a : Address w) (m : MiniTreeCode) : Finset (Pair w) :=
  {orient (addrExt a [m.red.1]) (slotSign (nodeSign σ a) m.red.1) (addrExt a [m.c,m.red.2]),
   orient (addrExt a [m.green.1]) (slotSign (nodeSign σ a) m.green.1) (addrExt a [m.c,m.green.2])}

/-- Source B insertion: retain the complete old subtree at the mini-tree's lone slot. -/
def Raw.opB {w : ℕ} (R : Raw w) (a : Address w) (m : MiniTreeCode) : Raw w :=
  let S := (R.tree a.1).subtreeAt a.2
  let mini := node3 fun i => if i = m.c then node3 (fun j => if j = m.lone then S else .leaf) else .leaf
  ⟨R.sig,Function.update R.tree a.1 ((R.tree a.1).setAt a.2 mini),
    R.pairs.image (fun p => (relocate a m.c m.lone p.1,relocate a m.c m.lone p.2)) ∪
      miniPairs R.sig a m⟩

/-- Raw branching order; a valid elementary source expansion adds exactly two. -/
def Raw.order {w : ℕ} (R : Raw w) : ℕ := ∑ j, (R.tree j).order

/-- Source typing data: every endpoint is a genuine leaf, and the pair set is
exactly a sign-oriented perfect matching of all leaves of the literal forest. -/
def Raw.Valid {w : ℕ} (R : Raw w) : Prop :=
  (∀ p ∈ R.pairs, p.1.2 ∈ (R.tree p.1.1).leaves ∧ p.2.2 ∈ (R.tree p.2.1).leaves ∧
    nodeSign R.sig p.1 = 1 ∧ nodeSign R.sig p.2 = -1) ∧
  (∀ ℓ : GLeaf R.tree, ∃! p : Pair w, p ∈ R.pairs ∧ (p.1 = ℓ.1 ∨ p.2 = ℓ.1))

/-- One actual elementary source expansion, with precisely its position guard. -/
inductive Expand {w : ℕ} : Raw w → Raw w → Prop
  | opA (R : Raw w) (x y : Address w) (c : MiniCplCode) :
      R.Valid → (x,y) ∈ R.pairs → Expand R (R.opA x y c)
  | opB (R : Raw w) (a : Address w) (m : MiniTreeCode) :
      R.Valid → a.2 ∈ (R.tree a.1).nodes → Expand R (R.opB a m)

/-- The prime predicate is the source's absence of an inverse elementary move. -/
def Prime {w : ℕ} (R : Raw w) : Prop := R.Valid ∧ ∀ S, ¬ Expand S R

/-- The source reconstruction relation: finitely many actual A/B expansions. -/
def Reconstructs {w : ℕ} (S R : Raw w) : Prop := Relation.ReflTransGen Expand S R

end WaveTurbulence.Reg.Skeleton
