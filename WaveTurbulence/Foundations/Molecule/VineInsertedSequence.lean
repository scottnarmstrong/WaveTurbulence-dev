/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailIndex
public import WaveTurbulence.Foundations.Molecule.VineLiteralSequences
import Mathlib.Tactic

/-! # Literal full-rung sequences supplied by the pinned insertion -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- The four labels of a vector, preserving repeated entries. -/
theorem four_labels {N : ℕ} (a b c d : Fin N) :
    (univ : Finset (Fin 4)).val.map (fun j => (![a,b,c,d] j).1)=
      {a.1}+{b.1}+{c.1}+{d.1} := by
  rw [Fin.univ_val_map]
  rfl

/-- The fresh rungs of one literal insertion are a full-rung sequence.
All incidence rows are proved from the pinned edge-list definition. -/
@[expose] def insertedSequence (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ))
    (k : ℕ) (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n) :
    LiteralFullRungSequence (insertRungs T s k) k where
  u := fun i => ⟨railAtom T.n s.1.1 s.1.2 k i,by
    rw [insertRungs_atoms]
    exact railAtom_lt _ _ _ _ _ _ (by omega) (by omega) (by omega)⟩
  v := fun i => ⟨railAtom (T.n+k) s.2.1 s.2.2 k i,by
    rw [insertRungs_atoms]
    exact railAtom_lt _ _ _ _ _ _ (by omega) (by omega) (by omega)⟩
  distinct := by
    intro i j hij
    have he := congrArg Fin.val hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        congr 1
        apply Fin.ext
        change railAtom T.n s.1.1 s.1.2 k (i.1+1)=
          railAtom T.n s.1.1 s.1.2 k (j.1+1) at he
        rw [railAtom_interior _ _ _ _ _ (by omega) (by omega),
          railAtom_interior _ _ _ _ _ (by omega) (by omega)] at he
        omega
      | inr j =>
        change railAtom T.n s.1.1 s.1.2 k (i.1+1)=
          railAtom (T.n+k) s.2.1 s.2.2 k (j.1+1) at he
        rw [railAtom_interior _ _ _ _ _ (by omega) (by omega),
          railAtom_interior _ _ _ _ _ (by omega) (by omega)] at he
        omega
    | inr i =>
      cases j with
      | inl j =>
        change railAtom (T.n+k) s.2.1 s.2.2 k (i.1+1)=
          railAtom T.n s.1.1 s.1.2 k (j.1+1) at he
        rw [railAtom_interior _ _ _ _ _ (by omega) (by omega),
          railAtom_interior _ _ _ _ _ (by omega) (by omega)] at he
        omega
      | inr j =>
        congr 1
        apply Fin.ext
        change railAtom (T.n+k) s.2.1 s.2.2 k (i.1+1)=
          railAtom (T.n+k) s.2.1 s.2.2 k (j.1+1) at he
        rw [railAtom_interior _ _ _ _ _ (by omega) (by omega),
          railAtom_interior _ _ _ _ _ (by omega) (by omega)] at he
        omega
  upper := by
    intro i hi hin
    rw [four_labels]
    change edgeListNeighbors _ (railAtom T.n s.1.1 s.1.2 k i)=
      {railAtom (T.n+k) s.2.1 s.2.2 k i}+
      {railAtom (T.n+k) s.2.1 s.2.2 k i}+
      {railAtom T.n s.1.1 s.1.2 k (i-1)}+
      {railAtom T.n s.1.1 s.1.2 k (i+1)}
    rw [railAtom_interior _ _ _ _ _ hi hin,
      railAtom_interior _ _ _ _ _ hi hin,
      insertRungs_neighbors_left T s k (i-1) (by omega) hT hs,
      railAtom_prev _ _ _ _ _ (by omega)]
    have hh : i+1=(i-1)+2 := by omega
    rw [hh,railAtom_next _ _ _ _ _ (by omega)]
    ac_rfl
  lower := by
    intro i hi hin
    rw [four_labels]
    change edgeListNeighbors _ (railAtom (T.n+k) s.2.1 s.2.2 k i)=
      {railAtom T.n s.1.1 s.1.2 k i}+
      {railAtom T.n s.1.1 s.1.2 k i}+
      {railAtom (T.n+k) s.2.1 s.2.2 k (i-1)}+
      {railAtom (T.n+k) s.2.1 s.2.2 k (i+1)}
    rw [railAtom_interior _ _ _ _ _ hi hin,
      railAtom_interior _ _ _ _ _ hi hin,
      insertRungs_neighbors_right T s k (i-1) (by omega) hT hs,
      railAtom_prev _ _ _ _ _ (by omega)]
    have hh : i+1=(i-1)+2 := by omega
    rw [hh,railAtom_next _ _ _ _ _ (by omega)]
    ac_rfl

end WaveTurbulence.Vine
