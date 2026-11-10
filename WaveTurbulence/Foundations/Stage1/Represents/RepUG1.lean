/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.FinalCount.RedSpliceUnitBlocks
import Mathlib.Tactic

/-!
# S2 REPRESENTS, UnitGap (1): every unit of a group has an external pair of the gap kind of the designated object

`HingeSpec G S a p` gives the external pair only for the unit containing the designated joint `a`.  `UnitSpec G S u p` is its
inner clause for an arbitrary unit `u`; `exists_unitSpec` produces it for every unit (units are disjoint, so the unit of
`HingeSpec` for `a := u.upper` is `u`), and `unitSpec_gapKind` is the proof of `hingeOrig_gapKind` with `u` general (the
designated joint `a` enters only through `IsDesig`): the gap of the pair `p` has the kind of the designated object.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w}

/-- The external pair of a given unit `u` (the inner clause of `HingeSpec`). -/
def UnitSpec (G : Garden w) (S : Finset (GBranch G.tree)) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j ∈ u.atoms,
    TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
    (∀ sk, (groupUnitsOf G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
      G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
      ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
    ((groupUnitsOf G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower))

theorem unit_eq_of_mem {S : Finset (GBranch G.tree)} {u u' : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units)
    (hu' : u' ∈ (groupUnitsOf G S).units) {a : GBranch G.tree} (ha : a ∈ u.atoms) (ha' : a ∈ u'.atoms) : u = u' := by
  by_contra hne
  have : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
  have := List.Pairwise.forall (groupUnitsOf G S).disj hu hu' hne
  exact Finset.disjoint_left.mp this ha ha'

theorem exists_unitSpec {S : Finset (GBranch G.tree)} {u : CLBlock G} (hu : u ∈ (groupUnitsOf G S).units) :
    ∃ p, UnitSpec G S u p := by
  obtain ⟨p, hp⟩ := exists_hingeSpec (S := S) (a := u.upper) ⟨u, hu, u.isBlock.2.1⟩
  obtain ⟨u', hu', hau, j, hj, rest⟩ := hp
  have he := unit_eq_of_mem hu hu' u.isBlock.2.1 hau
  subst he
  exact ⟨p, j, hj, rest⟩

end WaveTurbulence.Represents
