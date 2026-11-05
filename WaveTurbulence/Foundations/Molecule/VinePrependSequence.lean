/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Including one old doubled endpoint pair as the first actual rung -/

public section
namespace WaveTurbulence.Vine

/-- Prepend an external port and shift every old rail coordinate by one. -/
@[expose] def prependRail {V : Type*} (f : ℕ → V) (p : V) : ℕ → V
  | 0 => p
  | i+1 => f i

variable {V D : Type*}

/-- A start incidence row followed by all original rows forms an enlarged
one-sided full-rung sequence. -/
@[expose] def prependRail_rows {M : Molecule V D} (u v : ℕ → V) (p q : V) (n : ℕ)
    (hrow : ∀ i,1 ≤ i → i ≤ n → FourIncidences M (u i) ![v i,v i,u (i-1),u (i+1)])
    (h0 : FourIncidences M (u 0) ![v 0,v 0,p,u 1]) :
    ∀ i,1 ≤ i → i ≤ n+1 → FourIncidences M (prependRail u p i)
      ![prependRail v q i,prependRail v q i,prependRail u p (i-1),prependRail u p (i+1)] := by
  intro i hi hin
  cases i with
  | zero => omega
  | succ i =>
    cases i with
    | zero => exact h0
    | succ j =>
      have hh := hrow (j+1) (by omega) (by omega)
      simpa only [prependRail,Nat.add_sub_cancel] using hh

/-- Include the old initial doubled port pair as an actual first rung,
while the old final port pair remains external. Full endpoint distinctness
is primitive graph data, independent of any selected block. -/
@[expose] def FullRungSequence.prepend {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (p q : V)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => Q.u i.1)
      (fun i : Fin (n+2) => Q.v i.1)))
    (hu0 : FourIncidences M (Q.u 0) ![Q.v 0,Q.v 0,p,Q.u 1])
    (hv0 : FourIncidences M (Q.v 0) ![Q.u 0,Q.u 0,q,Q.v 1]) :
    FullRungSequence M (n+1) where
  u := prependRail Q.u p
  v := prependRail Q.v q
  distinct := by
    let e : Fin (n+1) ⊕ Fin (n+1) → Fin (n+2) ⊕ Fin (n+2) :=
      Sum.map (Fin.castLE (by omega)) (Fin.castLE (by omega))
    have he : Function.Injective e := Sum.map_injective.mpr
      ⟨Fin.castLE_injective _,Fin.castLE_injective _⟩
    intro i j hij
    apply he
    apply hd
    cases i <;> cases j <;> exact hij
  upper := prependRail_rows Q.u Q.v p q n Q.upper hu0
  lower := prependRail_rows Q.v Q.u q p n Q.lower hv0

/-- Include the old initial doubled port pair as an actual first rung,
while allowing the final ports to coincide (type II, F72).
Only the initial ports and actual old rungs must be distinct. -/
@[expose] def FullRungSequence.prependInitialDistinct {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (p q : V)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+1) => Q.u i.1)
      (fun i : Fin (n+1) => Q.v i.1)))
    (hu0 : FourIncidences M (Q.u 0) ![Q.v 0,Q.v 0,p,Q.u 1])
    (hv0 : FourIncidences M (Q.v 0) ![Q.u 0,Q.u 0,q,Q.v 1]) :
    FullRungSequence M (n+1) where
  u := prependRail Q.u p
  v := prependRail Q.v q
  distinct := by
    intro i j hij
    apply hd
    cases i <;> cases j <;> exact hij
  upper := prependRail_rows Q.u Q.v p q n Q.upper hu0
  lower := prependRail_rows Q.v Q.u q p n Q.lower hv0

end WaveTurbulence.Vine
