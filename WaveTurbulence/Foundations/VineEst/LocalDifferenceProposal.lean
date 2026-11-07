/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract

/-! # Proposed local-incidence witness for the garden inverse-unit proof

No new obligation is assumed or proved here. This property refines the
existing difference witness by recording its source incidence geometry.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The two actual incidences of an internal bond, or one of the two
external lower-joint labels. g is incoming and h=g-r is outgoing, since
the internal lower-joint flow is r. -/
def OriginAt (M : Molecule V D) (S : Finset V) (b : V)
    (p : Bond M S ⊕ Fin 2) (v : V) (out : Bool) : Prop :=
  match p with
  | .inl e => (M.atom e.1 = v ∧ M.out e.1 = out) ∨
      (M.atom (M.mate e.1) = v ∧ M.out (M.mate e.1) = out)
  | .inr j => v = b ∧ out = if j = 0 then false else true

/-- A difference may be replaced by an equal difference on the full flow
fiber. The witnesses are opposite incidences at a common actual atom.
This is molecule-level geometry, with no garden basis or coefficient claim. -/
def FullVineChart.HasLocalDifferences {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (A : FullVineChart M X S a b) : Prop :=
  ∀ i, ∃ p q : Bond M S ⊕ Fin 2,
    (∃ v ∈ S, ∃ out : Bool, OriginAt M S b p v out ∧ OriginAt M S b q v (!out)) ∧
    ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      A.chart g r k i = origin M S k.1 g r p-origin M S k.1 g r q

end WaveTurbulence.VineParamContract
