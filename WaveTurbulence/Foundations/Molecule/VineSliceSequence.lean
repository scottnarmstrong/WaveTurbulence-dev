/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRungSequences
import Mathlib.Tactic

/-! # Arbitrary contiguous slices of an actual full-rung sequence -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- Restrict a full-rung sequence to m rungs after its t-th rung. Both
new external ports are retained, including the zero-length slice case. -/
@[expose] def FullRungSequence.slice {M : Molecule V D} {n : ℕ}
    (Q : FullRungSequence M n) (t m : ℕ) (htm : t+m ≤ n) : FullRungSequence M m where
  u := fun i => Q.u (t+i)
  v := fun i => Q.v (t+i)
  distinct := by
    let e : Fin m ⊕ Fin m → Fin n ⊕ Fin n := Sum.map
      (fun i => ⟨t+i.1,by omega⟩) (fun i => ⟨t+i.1,by omega⟩)
    have he : Function.Injective e := by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          simp only [e,Sum.map_inl,Sum.inl.injEq] at hij
          have hh := congrArg Fin.val hij
          change t+i.1=t+j.1 at hh
          exact congrArg Sum.inl (Fin.ext (by omega))
        | inr j => cases hij
      | inr i =>
        cases j with
        | inl j => cases hij
        | inr j =>
          simp only [e,Sum.map_inr,Sum.inr.injEq] at hij
          have hh := congrArg Fin.val hij
          change t+i.1=t+j.1 at hh
          exact congrArg Sum.inr (Fin.ext (by omega))
    have hc := Q.distinct.comp he
    have hfun : Sum.elim (fun i : Fin m => Q.u (t+(i.1+1)))
        (fun i : Fin m => Q.v (t+(i.1+1)))=
        (Sum.elim (fun i : Fin n => Q.u (i.1+1)) (fun i : Fin n => Q.v (i.1+1))) ∘ e := by
      funext i
      cases i <;> simp only [e,Sum.map_inl,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,
        Function.comp_apply,Nat.add_assoc]
    rw [hfun]
    exact hc
  upper := by
    intro i hi hin
    have hh := Q.upper (t+i) (by omega) (by omega)
    simpa only [show t+i-1=t+(i-1) by omega,Nat.add_assoc] using hh
  lower := by
    intro i hi hin
    have hh := Q.lower (t+i) (by omega) (by omega)
    simpa only [show t+i-1=t+(i-1) by omega,Nat.add_assoc] using hh

end WaveTurbulence.Vine
