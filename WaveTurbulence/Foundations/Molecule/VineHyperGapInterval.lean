/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSliceSequence
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySequence
import Mathlib.Tactic

/-! # No selected hyper-block rung lies between two absent pairs -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Two absent rail pairs exclude every intervening full rung. The two
pairs may be original external ports, so this includes intervals touching
either end of the source ladder. -/
theorem hyperBlock_absent_interval (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {a b : V} (hH : Mole.IsHyperBlock M A a b) {n : ℕ}
    (Q : FullRungSequence M n) (l r : ℕ) (hlr : l < r) (hr : r ≤ n+1)
    (hul : Q.u l ∉ A) (hvl : Q.v l ∉ A) (hur : Q.u r ∉ A) (hvr : Q.v r ∉ A) :
    ∀ i,l < i → i < r → Q.u i ∉ A ∧ Q.v i ∉ A := by
  let E := Q.slice l (r-l-1) (by omega)
  have heq : l+(r-l-1+1)=r := by omega
  have hu0 : E.u 0 ∉ A := by change Q.u (l+0) ∉ A; simpa only [Nat.add_zero] using hul
  have hv0 : E.v 0 ∉ A := by change Q.v (l+0) ∉ A; simpa only [Nat.add_zero] using hvl
  have huN : E.u (r-l-1+1) ∉ A := by change Q.u (l+(r-l-1+1)) ∉ A; simpa only [heq] using hur
  have hvN : E.v (r-l-1+1) ∉ A := by change Q.v (l+(r-l-1+1)) ∉ A; simpa only [heq] using hvr
  have hh := hyperBlock_empty_ended_sequence M hM hH E hu0 hv0 huN hvN
  intro i hli hir
  have hi := hh (i-l) (by omega) (by omega)
  change Q.u (l+(i-l)) ∉ A ∧ Q.v (l+(i-l)) ∉ A at hi
  simpa only [show l+(i-l)=i by omega] using hi

end WaveTurbulence.Vine
