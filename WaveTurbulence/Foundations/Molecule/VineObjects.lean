/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondEdits

/-! # Draft vine-like objects (TARGET defvine, defblock and vinechainlem)

These definitions supplement, without changing, the pinned B2 vine draft.
A chain records its ingredients in order. An HV is the adjoint of one vine;
an HVC has at least two ingredients. A DV shares exactly its two joints,
and therefore may share the bond between those joints.
-/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- One ingredient with ordered joints. The vine type remains existential. -/
@[expose] def IsSomeVine (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ X : VineType, M.IsVine X S a b

/-- Ordered concatenation of vines, sharing just the joining joint at each
step. Endpoint closure is handled separately by the hyper-adjoint operation. -/
inductive Chain (M : Molecule V D) : Finset V → V → V → ℕ → Prop
  | single {S a b} : IsSomeVine M S a b → Chain M S a b 1
  | append {S T a b c n} : Chain M S a b n → IsSomeVine M T b c →
      S ∩ T = {b} → a ≠ c → Chain M (S ∪ T) a c (n+1)

/-- TARGET defvine: a VC is a block formed by one or more vine ingredients. -/
@[expose] def IsVC (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsBlock S a b ∧ ∃ n, Chain M S a b n

/-- TARGET defvine: an HV is the adjoint of a single vine. The deleted
bond is remembered so multiplicities cause no ambiguity. -/
@[expose] def IsHV (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧ IsSomeVine (Mole.eraseBond M e) S a b

/-- TARGET defvine: an HVC is an adjoint VC with at least two ingredients.
In particular a lone HV is not an HVC by this construction. -/
@[expose] def IsHVC (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧
    (Mole.eraseBond M e).IsBlock S a b ∧
    ∃ n, 2 ≤ n ∧ Chain (Mole.eraseBond M e) S a b n

/-- TARGET vinechainlem: two type-V vines with the same two joints and
no other common atom. Sharing the joint-to-joint bond is allowed. -/
@[expose] def IsDV (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ A B : Finset V, M.IsVine .V A a b ∧ M.IsVine .V B a b ∧
    A ∩ B = {a,b} ∧ S = A ∪ B

/-- TARGET defvine: the three classes called vine-like (DV is excluded). -/
@[expose] def IsVineLike (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  IsVC M S a b ∨ IsHV M S a b ∨ IsHVC M S a b

omit [DecidableEq D] in
/-- Every actual vine is a one-ingredient VC. -/
theorem isVine_isVC {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : IsVC M S a b :=
  ⟨h.1,1,Chain.single ⟨X,h⟩⟩

omit [DecidableEq D] in
/-- Every chain has at least one ingredient. -/
theorem chain_pos {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain M S a b n) : 1 ≤ n := by
  induction h with
  | single => exact le_rfl
  | append _ _ _ _ _ => omega

/-- Hyper-vines are actual hyper-blocks in the half-edge sense. -/
theorem isHV_isHyperBlock {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsHV M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e,he,X,hX⟩ := h
  exact ⟨e,he,hX.1⟩

/-- Hyper-vine-chains are actual hyper-blocks. -/
theorem isHVC_isHyperBlock {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsHVC M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e,he,hB,_⟩ := h
  exact ⟨e,he,hB⟩

end WaveTurbulence.Vine
