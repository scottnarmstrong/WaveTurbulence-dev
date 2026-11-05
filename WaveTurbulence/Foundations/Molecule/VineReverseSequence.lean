/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Reversing full-rung sequence traversal without changing actual bonds -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- Reverse the two rail entries of a full four-dart row. -/
@[expose] def FourIncidences.reverseRails {M : Molecule V D} {x y p q : V}
    (R : FourIncidences M x ![y,y,p,q]) : FourIncidences M x ![y,y,q,p] where
  dart := fun i => R.dart (Equiv.swap (2 : Fin 4) 3 i)
  injective := R.injective.comp (Equiv.swap (2 : Fin 4) 3).injective
  atom_eq := fun i => R.atom_eq _
  neighbor_eq := by
    intro i
    rw [R.neighbor_eq]
    fin_cases i <;> norm_num [Equiv.swap_apply_def]

/-- Traverse a full-rung sequence from its opposite end, retaining both
external ports. Values beyond the final port use the displayed truncated
natural subtraction and are never used as actual rung coordinates. -/
@[expose] def FullRungSequence.reverse {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) : FullRungSequence M n where
  u := fun i => Q.u (n+1-i)
  v := fun i => Q.v (n+1-i)
  distinct := by
    let e : Fin n ⊕ Fin n → Fin n ⊕ Fin n := Sum.map Fin.rev Fin.rev
    have he : Function.Injective e :=
      Sum.map_injective.mpr ⟨Fin.rev_injective,Fin.rev_injective⟩
    have hc := Q.distinct.comp he
    have hfun : Sum.elim (fun i : Fin n => Q.u (n+1-(i.1+1)))
        (fun i : Fin n => Q.v (n+1-(i.1+1)))=
        (Sum.elim (fun i : Fin n => Q.u (i.1+1))
          (fun i : Fin n => Q.v (i.1+1))) ∘ e := by
      funext i
      cases i with
      | inl i =>
        change Q.u (n+1-(i.1+1))=Q.u ((Fin.rev i).1+1)
        congr 1
        simp only [Fin.val_rev]
        omega
      | inr i =>
        change Q.v (n+1-(i.1+1))=Q.v ((Fin.rev i).1+1)
        congr 1
        simp only [Fin.val_rev]
        omega
    rw [hfun]
    exact hc
  upper := by
    intro i hi hin
    have hh := (Q.upper (n+1-i) (by omega) (by omega)).reverseRails
    simpa only [show n+1-i+1=n+1-(i-1) by omega,
      show n+1-i-1=n+1-(i+1) by omega] using hh
  lower := by
    intro i hi hin
    have hh := (Q.lower (n+1-i) (by omega) (by omega)).reverseRails
    simpa only [show n+1-i+1=n+1-(i-1) by omega,
      show n+1-i-1=n+1-(i+1) by omega] using hh

end WaveTurbulence.Vine
