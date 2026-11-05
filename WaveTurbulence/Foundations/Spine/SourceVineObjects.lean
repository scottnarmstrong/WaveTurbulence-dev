/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
/-! Source vine-like object definitions copied from the completed VINES interface.
Only the namespace and the definitionally identical Molecule.eraseBond adapter change. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
/-- One ingredient with ordered joints. The vine type remains existential. -/
def IsSomeVine (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ X : VineType, M.IsVine X S a b

/-- Ordered concatenation of vines, sharing just the joining joint at each
step. Endpoint closure is handled separately by the hyper-adjoint operation. -/
inductive Chain (M : Molecule V D) : Finset V → V → V → ℕ → Prop
  | single {S a b} : IsSomeVine M S a b → Chain M S a b 1
  | append {S T a b c n} : Chain M S a b n → IsSomeVine M T b c →
      S ∩ T = {b} → a ≠ c → Chain M (S ∪ T) a c (n+1)

/-- TARGET defvine: a VC is a block formed by one or more vine ingredients. -/
def IsVC (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  M.IsBlock S a b ∧ ∃ n, Chain M S a b n

/-- TARGET defvine: an HV is the adjoint of a single vine. The deleted
bond is remembered so multiplicities cause no ambiguity. -/
def IsHV (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧ IsSomeVine (Molecule.eraseBond M e) S a b

/-- TARGET defvine: an HVC is an adjoint VC with at least two ingredients.
In particular a lone HV is not an HVC by this construction. -/
def IsHVC (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ e : D, M.ends e = s(a,b) ∧
    (Molecule.eraseBond M e).IsBlock S a b ∧
    ∃ n, 2 ≤ n ∧ Chain (Molecule.eraseBond M e) S a b n

/-- TARGET vinechainlem: two type-V vines with the same two joints and
no other common atom. Sharing the joint-to-joint bond is allowed. -/
def IsDV (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  ∃ A B : Finset V, M.IsVine .V A a b ∧ M.IsVine .V B a b ∧
    A ∩ B = {a,b} ∧ S = A ∪ B

/-- TARGET defvine: the three classes called vine-like (DV is excluded). -/
def IsVineLike (M : Molecule V D) (S : Finset V) (a b : V) : Prop :=
  IsVC M S a b ∨ IsHV M S a b ∨ IsHVC M S a b

/-- Actual source data for a hyper-vine-like object, retaining the bond
which defines its adjoint VC and therefore its decorated gap. -/
structure HyperLikeRealization (M : Molecule V D) (S : Finset V) (a b : V) where
  added : D
  ends_eq : M.ends added=s(a,b)
  adjoint : IsVC (Molecule.eraseBond M added) S a b


end WaveTurbulence.LGSpine.SourceVine
