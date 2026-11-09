/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.Gen

/-!
# The finite parametric family (N2 Lemma 1.7 parameters with Lemma 1.8's bound)

* `JParam.Valid p j`: a normalized joint placement on bonds of `genC p` such that the block `genB p j` has no
  triple bond (N2 Lemma 1.7: "the joints subdivide copies of bonds so that `B` has no triple bond");
* `cparams`: all valid closure parameters with at most 11 atoms (`k + k' ≤ 4`);
* `jparams p`: all valid joint placements on `genC p`;
* `instList`: the instance family (every T-vine with at most 13 atoms is isomorphic to one of them:
  `Checker.Complete`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

/-- Add a pair unless already present. -/
def addPair (q : ℕ × ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := if l.contains q then l else q :: l

/-- The bonds `x–y` (`x < y`) of a bond list, each once. -/
def pairsOf (es : Edges) : List (ℕ × ℕ) :=
  es.foldr (fun e l => if e.1 < e.2 then addPair e l else if e.2 < e.1 then addPair (e.2, e.1) l else l) []

/-- **Valid joint placement**: normalized (`x < y` on each subdivided bond; for two joints the bonds in
lexicographic order), on bonds of `genC p` (a bond subdivided twice must have multiplicity ≥ 2), and the block
has no triple bond. -/
def JParam.Valid (p : CParam) (j : JParam) : Prop :=
  (match j with
    | .two x₁ y₁ x₂ y₂ => x₁ < y₁ ∧ x₂ < y₂ ∧ (x₁ < x₂ ∨ (x₁ = x₂ ∧ y₁ ≤ y₂)) ∧ mult (genC p) x₁ y₁ ≠ 0 ∧
        mult (eraseOne (genC p) x₁ y₁) x₂ y₂ ≠ 0
    | .one x y => x < y ∧ mult (genC p) x y ≠ 0) ∧
  multLe2 (genB p j) = true

/-- All valid closure parameters with `k + k' ≤ 4` (closures with at most 11 atoms). -/
def cparams : List CParam :=
  ((List.range 5).map fun k => (⟨k, none⟩ : CParam)) ++
    (List.range 5).flatMap fun k => (List.range 5).flatMap fun k' =>
      if 1 ≤ k && 1 ≤ k' && k + k' ≤ 4 then
        ((pairsOf (gen1 k)).filter fun q => mult (gen1 k) q.1 q.2 ≤ 2).map fun q => (⟨k, some (q.1, q.2, k')⟩ : CParam)
      else []

/-- All candidate joint placements on `genC p`, filtered by validity. -/
def jparams (p : CParam) : List JParam :=
  let ps := pairsOf (genC p)
  let two := ps.flatMap fun q₁ => ps.filterMap fun q₂ =>
    if (q₁.1 < q₂.1 || (q₁.1 == q₂.1 && q₁.2 ≤ q₂.2)) &&
        mult (eraseOne (genC p) q₁.1 q₁.2) q₂.1 q₂.2 != 0 then some (JParam.two q₁.1 q₁.2 q₂.1 q₂.2) else none
  let one := ps.map fun q => JParam.one q.1 q.2
  (two ++ one).filter fun j => multLe2 (genB p j)

/-- **The instance family**: every valid closure with at most 11 atoms, with every valid joint placement. -/
def instList : List (CParam × JParam) := cparams.flatMap fun p => (jparams p).map fun j => (p, j)

end WaveTurbulence.TVine.Checker
