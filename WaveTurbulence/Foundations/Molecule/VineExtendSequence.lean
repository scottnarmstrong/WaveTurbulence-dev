/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Extending a full-rung sequence by its two old endpoint pairs -/

public section
namespace WaveTurbulence.Vine

/-- Shift a rail by one and supply new external ports. Its two old ports
become the first and last actual rung atoms. -/
@[expose] def extendRail {V : Type*} (f : ℕ → V) (p q : V) (n i : ℕ) : V :=
  if i=0 then p else if i ≤ n+2 then f (i-1) else q

/-- The new first external port has index zero. -/
theorem extendRail_zero {V : Type*} (f : ℕ → V) (p q : V) (n : ℕ) :
    extendRail f p q n 0=p := by simp [extendRail]

/-- Every old rail index shifts by exactly one. -/
theorem extendRail_succ {V : Type*} (f : ℕ → V) (p q : V) (n i : ℕ) (hi : i ≤ n+1) :
    extendRail f p q n (i+1)=f i := by
  have hn : i+1 ≠ 0 := by omega
  have hb : i+1 ≤ n+2 := by omega
  simp only [extendRail,hn,ite_false,hb,ite_true,Nat.add_sub_cancel]

/-- The new final external port follows both added endpoint rungs. -/
theorem extendRail_last {V : Type*} (f : ℕ → V) (p q : V) (n : ℕ) :
    extendRail f p q n (n+3)=q := by
  have hn : n+3 ≠ 0 := by omega
  have hb : ¬n+3 ≤ n+2 := by omega
  simp only [extendRail,hn,hb,ite_false]

/-- Internal positions of the extended rail are the shifted old positions. -/
theorem extendRail_internal {V : Type*} (f : ℕ → V) (p q : V) (n i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ n+2) : extendRail f p q n i=f (i-1) := by
  have hn : i ≠ 0 := by omega
  simp only [extendRail,hn,ite_false,hin,ite_true]

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Shift the internal incidence rows and attach the two old endpoint rows. -/
@[expose] def extendRail_rows {M : Molecule V D} (u v : ℕ → V) (p q r s : V) (n : ℕ)
    (hrow : ∀ i,1 ≤ i → i ≤ n → FourIncidences M (u i) ![v i,v i,u (i-1),u (i+1)])
    (h0 : FourIncidences M (u 0) ![v 0,v 0,p,u 1])
    (hN : FourIncidences M (u (n+1)) ![v (n+1),v (n+1),u n,q]) :
    ∀ i,1 ≤ i → i ≤ n+2 → FourIncidences M (extendRail u p q n i)
      ![extendRail v r s n i,extendRail v r s n i,
        extendRail u p q n (i-1),extendRail u p q n (i+1)] := by
  intro i hi hin
  by_cases hfirst : i=1
  · subst i
    simpa only [extendRail_internal u p q n 1 (by omega) (by omega),
      extendRail_internal v r s n 1 (by omega) (by omega),
      extendRail_internal u p q n 2 (by omega) (by omega),
      show (1:ℕ)-1=0 from rfl,extendRail_zero,show (2:ℕ)-1=1 from rfl] using h0
  · by_cases hlast : i=n+2
    · subst i
      simpa only [show n+2-1=n+1 by omega,show n+2+1=n+3 by omega,
        extendRail_internal u p q n (n+2) (by omega) le_rfl,
        extendRail_internal v r s n (n+2) (by omega) le_rfl,
        extendRail_internal u p q n (n+1) (by omega) (by omega),
        Nat.add_sub_cancel,extendRail_last] using hN
    · have hh := hrow (i-1) (by omega) (by omega)
      simpa only [extendRail_internal u p q n i hi hin,
        extendRail_internal v r s n i hi hin,
        extendRail_internal u p q n (i-1) (by omega) (by omega),
        extendRail_internal u p q n (i+1) (by omega) (by omega),Nat.add_sub_cancel,show i-1+1=i by omega] using hh

/-- Incorporate two old doubled endpoint pairs into a full-rung sequence.
The assumptions are literal incidence and distinct-atom data; they assert
no property of a selected block. -/
@[expose] def FullRungSequence.extend {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (p q r s : V)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => Q.u i.1)
      (fun i : Fin (n+2) => Q.v i.1)))
    (hu0 : FourIncidences M (Q.u 0) ![Q.v 0,Q.v 0,p,Q.u 1])
    (hv0 : FourIncidences M (Q.v 0) ![Q.u 0,Q.u 0,r,Q.v 1])
    (huN : FourIncidences M (Q.u (n+1)) ![Q.v (n+1),Q.v (n+1),Q.u n,q])
    (hvN : FourIncidences M (Q.v (n+1)) ![Q.u (n+1),Q.u (n+1),Q.v n,s]) :
    FullRungSequence M (n+2) where
  u := extendRail Q.u p q n
  v := extendRail Q.v r s n
  distinct := by
    intro i j he
    apply hd
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa only [Sum.elim_inl,
          extendRail_succ Q.u p q n i.1 (by omega),
          extendRail_succ Q.u p q n j.1 (by omega)] using he
      | inr j => simpa only [Sum.elim_inl,Sum.elim_inr,
          extendRail_succ Q.u p q n i.1 (by omega),
          extendRail_succ Q.v r s n j.1 (by omega)] using he
    | inr i =>
      cases j with
      | inl j => simpa only [Sum.elim_inl,Sum.elim_inr,
          extendRail_succ Q.v r s n i.1 (by omega),
          extendRail_succ Q.u p q n j.1 (by omega)] using he
      | inr j => simpa only [Sum.elim_inr,
          extendRail_succ Q.v r s n i.1 (by omega),
          extendRail_succ Q.v r s n j.1 (by omega)] using he
  upper := extendRail_rows Q.u Q.v p q r s n Q.upper hu0 huN
  lower := extendRail_rows Q.v Q.u r s p q n Q.lower hv0 hvN

end WaveTurbulence.Vine
