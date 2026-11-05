/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVIIRedProtectedData
import Mathlib.Tactic

/-! # Type-VII red old ports are joined outside its removed side -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The complete source red rails give protected paths between the
old ports, for every rung count, including zero. -/
theorem VineRealization.typeVII_red_protected_paths {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b) (hM : M.IsMolecule)
    (kr kc kg : ℕ) (hks : R.k=[kr,kc,kg]) :
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom (2 : Fin 11)).1 (R.coreAtom (7 : Fin 11)).1 ∧
    Relation.EqvGen (ProtectedSingleAdj M S (R.selectedAtoms (sideLabels (11+2*kr) kc))
      (R.coreAtom (7 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1)
      (R.coreAtom (3 : Fin 11)).1 (R.coreAtom (8 : Fin 11)).1 := by
  obtain ⟨Q,hmem,hports,hlabels,H,hzero⟩ := R.typeVII_red_protected_data kr kc kg hks
  have hloc : VineType.VII.template.slots.zip R.k=
      []++(((2,7),(3,8)),kr)::[(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] := by rw [hks]; rfl
  have hp := R.slot_protected_paths hM [] [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr
    hloc Q hmem hports (by simpa only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] using hlabels) H hzero
  have eqCore (v : V) (hv : v ∈ S) (i : Fin 11) (hi : R.f v=i.1) : v=(R.coreAtom i).1 :=
    R.injOn hv (R.coreAtom i).2 (hi.trans (R.label_coreAtom i).symm)
  have hu0 := eqCore (Q.u 0) (hmem 0).1 (2 : Fin 11) hports.1
  have hv0 := eqCore (Q.v 0) (hmem 0).2 (3 : Fin 11) hports.2.1
  have huN := eqCore (Q.u (kr+1)) (hmem (kr+1)).1 (7 : Fin 11) hports.2.2.1
  have hvN := eqCore (Q.v (kr+1)) (hmem (kr+1)).2 (8 : Fin 11) hports.2.2.2
  simpa only [hu0,hv0,huN,hvN] using hp

end WaveTurbulence.Vine
