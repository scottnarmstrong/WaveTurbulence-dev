/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TypeIIFullSequence
public import WaveTurbulence.Foundations.Molecule.EndRungData

/-!
# Extract the actual rung adjacent to either joint of every type-II vine

TARGET molecpl (2), F72. The producer uses the literal current B2 vine
predicate and the accepted M4 construction, retaining all actual atom
memberships. Zero inserted rungs is allowed and gives m=1.
-/

public section
namespace WaveTurbulence.Molecpl
open Vine Finset TTree
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Every actual current type-II vine supplies its end-rung incidence geometry at either chosen joint. -/
theorem typeII_end_rung (hM : M.IsMolecule) {S : Finset V} {a b : V}
    (hV : M.IsVine .II S a b) : Nonempty (EndRungData M S a b) := by
  classical
  obtain ⟨_hB,⟨R⟩⟩ := Vine.isVine_iff_realization.mp hV
  have hlen : R.k.length=1 := R.length_eq
  obtain ⟨k,hk⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨Q,hu0,hv0,huN,hvN,hmem,_hcover⟩ := typeII_full_sequence_with_membership R k hk
  have hb : b ∈ S := hV.1.2.2.1
  have hfb : R.f b ∈ ({0,1} : Finset ℕ) := by
    rw [← R.joints_eq]
    exact mem_insert_of_mem (mem_singleton_self _)
  have ha : a ∈ S := hV.1.2.1
  have hfa : R.f a ∈ ({0,1} : Finset ℕ) := by
    rw [← R.joints_eq]
    exact mem_insert_self _ _
  have hne : R.f a ≠ R.f b := fun he => hV.1.2.2.2.1 (R.injOn ha hb he)
  simp only [mem_insert,mem_singleton] at hfa
  simp only [mem_insert,mem_singleton] at hfb
  rcases hfb with hfb | hfb
  · have he : (R.coreAtom (0:Fin 4)).1=b :=
      R.injOn (R.coreAtom (0:Fin 4)).2 hb ((R.label_coreAtom (0:Fin 4)).trans hfb.symm)
    have hfa1 : R.f a = 1 := hfa.resolve_left (by simpa only [hfb] using hne)
    have hea : (R.coreAtom (1:Fin 4)).1=a :=
      R.injOn (R.coreAtom (1:Fin 4)).2 ha ((R.label_coreAtom (1:Fin 4)).trans hfa1.symm)
    exact endRung_at_first hM hV.1 (by omega : 1 ≤ k+1) Q hmem (hu0.trans he) (hv0.trans he) (huN.trans hea) (hvN.trans hea)
  · have he : (R.coreAtom (1:Fin 4)).1=b :=
      R.injOn (R.coreAtom (1:Fin 4)).2 hb ((R.label_coreAtom (1:Fin 4)).trans hfb.symm)
    have hfa0 : R.f a = 0 := hfa.resolve_right (by simpa only [hfb] using hne)
    have hea : (R.coreAtom (0:Fin 4)).1=a :=
      R.injOn (R.coreAtom (0:Fin 4)).2 ha ((R.label_coreAtom (0:Fin 4)).trans hfa0.symm)
    exact endRung_at_last hM hV.1 (by omega : 1 ≤ k+1) Q hmem (huN.trans he) (hvN.trans he) (hu0.trans hea) (hv0.trans hea)

/-- The source garden case has no additional molecule-axiom or local-incidence premise. -/
theorem garden_typeII_end_rung {w : ℕ} (G : Garden w)
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) : Nonempty (EndRungData G.molecule S a b) :=
  typeII_end_rung G.molecule (Mole.garden_isMolecule G) hV

end WaveTurbulence.Molecpl
