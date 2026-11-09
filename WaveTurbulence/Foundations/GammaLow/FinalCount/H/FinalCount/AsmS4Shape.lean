/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmS4Shape
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmS4Shape`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY: named inputs owned by S4-SHAPE (M0-level).**

`PieceKill P N`: the darts of `M₀` removed by a Step-1 vine cut along the collected object `P` with node darts `N = (x₁,x₂,y₁,y₂)`:
all darts at an atom of `P`, except that at a joint only the two node darts at that joint are removed (the other darts of a joint are
moved to the fresh joint, and for a hyper-object the retained designated bond is among them).  `ConnAvoid M₀ Kd a b`: `a`, `b` are joined
by a chain of bonds of `M₀` none of whose darts (nor mates) lies in `Kd`.

`HostConn` (NAMED INPUT, owner S4-SHAPE; TARGET Lemma subsetvc, `subsetvc_simultaneous_removal_connected`): after the Step-1 vine
removals along pairwise atom-disjoint collected objects `ps`, and the removal of the interior atom `x` of a three-atom collected
object `U = {a, x, b}` all of whose bonds at `x` go to `a, b`, the joints `a`, `b` stay joined. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The darts of `M₀` removed by the vine cut along `P` with node darts `N`. -/
def PieceKill {M₀ : Molecule V D₀} (P : Src.Object Src.γL M₀) (N : Quad D₀) : Set D₀ :=
  {z | M₀.atom z ∈ P.atoms ∧ ((M₀.atom z = P.upper ∨ M₀.atom z = P.lower) →
      (z = N.1 ∨ z = N.2.1 ∨ z = N.2.2.1 ∨ z = N.2.2.2))}

/-- The interior atoms of a piece (all atoms but the joints). -/
def PieceInt {M₀ : Molecule V D₀} (P : Src.Object Src.γL M₀) (v : V) : Prop := v ∈ P.atoms ∧ v ≠ P.upper ∧ v ≠ P.lower

/-- The data of a removed piece: `P` collected for `κ`, the node darts are `ContainsDart` darts of `P`, at the joints of `P`
(the data of `HStep1R.vine`): two distinct node darts at each joint. -/
def PieceData {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d)
    (κ : D₀ → (Fin d → ℤ)) (p : Src.Object Src.γL M₀ × Quad D₀) : Prop :=
  Collected C (Un κ) L γ η w κ p.1 ∧
    (p.1.ContainsDart p.2.1 ∧ p.1.ContainsDart p.2.2.1 ∧ p.1.ContainsDart p.2.2.2.1 ∧ p.1.ContainsDart p.2.2.2.2) ∧
    ((M₀.atom p.2.1 = p.1.upper ∧ M₀.atom p.2.2.2.1 = p.1.lower) ∨
      (M₀.atom p.2.1 = p.1.lower ∧ M₀.atom p.2.2.2.1 = p.1.upper)) ∧
    (M₀.atom p.2.2.1 = M₀.atom p.2.1 ∧ M₀.atom p.2.2.2.2 = M₀.atom p.2.2.2.1 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.2.2.1 ≠ p.2.2.2.2)

/-- **NAMED INPUT (owner S4-SHAPE): host connectivity after Step-1 vine removals.** -/
def HostConn (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (L γ η : ℝ) (w : Mom d)
    (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (ps : List (Src.Object Src.γL M₀ × Quad D₀)) (U : Src.Object Src.γL M₀) (a x b : V),
    (∀ p ∈ ps, PieceData C Un L γ η w κ p) → ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    (∀ p ∈ ps, Disjoint p.1.atoms U.atoms) → Collected C (Un κ) L γ η w κ U → U.atoms = {a, x, b} →
    a ≠ x → x ≠ b → a ≠ b → (∀ z, M₀.atom z = x → M₀.atom (M₀.mate z) = a ∨ M₀.atom (M₀.mate z) = b) →
    ConnAvoid M₀ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x}) a b

end WaveTurbulence.GammaLow.FinalCount.H
