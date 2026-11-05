/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms

/-! # Transfer of excluded core atoms to actual label predicates -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Excluding two actual core atoms excludes their labels everywhere in
the outer vine, by injectivity of the pinned realization. -/
theorem VineRealization.exclude_core_pair {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (i j : Fin X.template.n)
    {A : Finset V} (hi : (R.coreAtom i).1 ∉ A) (hj : (R.coreAtom j).1 ∉ A) :
    ∀ v ∈ S,R.f v=i.1 ∨ R.f v=j.1 → v ∉ A := by
  intro v hv hlabel
  rcases hlabel with h | h
  · have he : v=(R.coreAtom i).1 := R.injOn hv (R.coreAtom i).2 (h.trans (R.label_coreAtom i).symm)
    simpa only [he] using hi
  · have he : v=(R.coreAtom j).1 := R.injOn hv (R.coreAtom j).2 (h.trans (R.label_coreAtom j).symm)
    simpa only [he] using hj

end WaveTurbulence.Vine
