/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreBondCounts
public import WaveTurbulence.Foundations.Molecule.VineRealizationInverse
import Mathlib.Tactic

/-! # The original core atoms inside an arbitrarily expanded actual vine -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Expansion never decreases the allocated atom range. -/
theorem template_n_le_expand (X : VineType) (ks : List ℕ) : X.template.n ≤ (X.expand ks).n := by
  unfold VineType.expand
  rw [fold_insertRungs_atoms]
  omega

/-- The actual atom carrying an original finite core index. -/
@[expose] noncomputable def VineRealization.coreAtom {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i : Fin X.template.n) : S :=
  R.atomAt ⟨i.1,lt_of_lt_of_le i.2 (template_n_le_expand X R.k)⟩

/-- The core atom keeps its original literal index through all insertions. -/
theorem VineRealization.label_coreAtom {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i : Fin X.template.n) :
    R.f (R.coreAtom i)=i.1 := R.label_atomAt _

/-- Different original core names remain different actual atoms. -/
theorem VineRealization.coreAtom_injective {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) :
    Function.Injective (fun i => (R.coreAtom i).1) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg R.f he
  simpa only [R.label_coreAtom] using hh

/-- Every doubled literal core edge supplies two distinct actual darts,
for arbitrary rung counts in every slot. -/
theorem VineRealization.core_twoIncidences {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i j : Fin X.template.n)
    (hc : 2 ≤ X.template.bonds.count (i.1,j.1)) :
    Nonempty (TwoIncidences M (R.coreAtom i).1 (R.coreAtom j).1) := by
  apply R.twoIncidences_of_edge_count (R.coreAtom i).2 (R.coreAtom j).2
  rw [R.label_coreAtom,R.label_coreAtom]
  exact hc.trans (expand_core_double_count X R.k (i.1,j.1) hc)

end WaveTurbulence.Vine
