/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIIIData
public import WaveTurbulence.Foundations.Molecule.VineHyperCoreProfiles
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySlots
public import WaveTurbulence.Foundations.Molecule.VineCapPrefixConstruction
import Mathlib.Tactic

/-! # Source cap construction for every contained type-VIII hyper-block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, source cap construction in type VIII. Old-core cut
classification and the actual slot incidences determine all cap-prefix data. -/
theorem typeVIII_hyper_cap_data (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .VIII S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ n r,Nonempty (CapPrefixData M A n r) := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  let c : Fin 11 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 11) : R.f (c i)=i.1 := R.label_coreAtom i
  have hlen : R.k.length=2 := R.length_eq
  obtain ⟨kr,kc,hks⟩ := List.length_eq_two.mp hlen
  obtain ⟨T,hd,Q,hmem,hports,hlabels,hreverse⟩ := typeVIII_side_data M R kr kc hks
  obtain ⟨W,hW,hprof⟩ := hyperBlock_core_profile M hM R hS hAS hH
  have hw : W=({8,9,10} : Finset ℕ) ∨ W=({6,7,8,9,10} : Finset ℕ) := by
    simpa only [hyperCoreSets,List.mem_cons,List.not_mem_nil,or_false] using hW
  have hwlo : ({8,9,10} : Finset ℕ) ⊆ W := by
    rcases hw with hw | hw <;> subst W <;> decide
  have hwhi : W ⊆ ({6,7,8,9,10} : Finset ℕ) := by
    rcases hw with hw | hw <;> subst W <;> decide
  have hcore (z : V) (hz : z ∈ S) (hi : R.f z<11) : z ∈ A ↔ R.f z ∈ W := hprof z hz hi
  have hsel (i : Fin 11) (hi : i.1=8 ∨ i.1=9 ∨ i.1=10) : c i ∈ A := by
    apply (hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mpr
    rw [hlabelc]
    apply hwlo
    simpa only [mem_insert,mem_singleton] using hi
  have habs (i : Fin 11) (hi : i.1 ≠ 6 ∧ i.1 ≠ 7 ∧ i.1 ≠ 8 ∧ i.1 ≠ 9 ∧ i.1 ≠ 10) : c i ∉ A := by
    intro hz
    have hh := hwhi ((hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mp hz)
    rw [hlabelc] at hh
    simp only [mem_insert,mem_singleton] at hh
    omega
  have hred := hyperBlock_empty_slot_from_ports M hM R hH []
    [(((6,8),(7,9)),kc)] ((2,4),(3,5)) kr (by rw [hks]; rfl) (by
      intro z hz hl hzA
      dsimp only at hl
      have hi : R.f z<11 := by rcases hl with h | h | h | h <;> omega
      have hh := hwhi ((hcore z hz hi).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      omega)
  dsimp only [List.foldl_nil,VineType.template] at hred
  have hregion : ∀ z ∈ A,z=c 10 ∨ z=c 8 ∨ z=c 9 ∨
      ∃ i,1 ≤ i ∧ i ≤ kc+1 ∧ (z=T.ladder.u i ∨ z=T.ladder.v i) := by
    intro z hzA
    have hz := hAS hzA
    have hzn := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hz)
    rw [hks,expand_atoms_exact .VIII [kr,kc] rfl] at hzn
    simp only [VineType.template,List.sum_cons,List.sum_nil,Nat.add_zero] at hzn
    by_cases hold : R.f z<11
    · have hh := hwhi ((hcore z hz hold).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h | h
      · have he : z=Q.u 0 := R.injOn hz (hmem 0).1 (h.trans (by rw [hports.1,hlabelc]; rfl))
        exact Or.inr (Or.inr (Or.inr ⟨kc+1,by omega,le_rfl,
          Or.inl (he.trans (hreverse 0 (by omega)).1.symm)⟩))
      · have he : z=Q.v 0 := R.injOn hz (hmem 0).2 (h.trans (by rw [hports.2.1,hlabelc]; rfl))
        exact Or.inr (Or.inr (Or.inr ⟨kc+1,by omega,le_rfl,
          Or.inr (he.trans (hreverse 0 (by omega)).2.symm)⟩))
      · exact Or.inr (Or.inl (R.injOn hz (R.coreAtom (8 : Fin 11)).2 (h.trans (hlabelc 8).symm)))
      · exact Or.inr (Or.inr (Or.inl (R.injOn hz (R.coreAtom (9 : Fin 11)).2 (h.trans (hlabelc 9).symm))))
      · exact Or.inl (R.injOn hz (R.coreAtom (10 : Fin 11)).2 (h.trans (hlabelc 10).symm))
    · by_cases hleft : R.f z<11+2*kr
      · exact False.elim (hred z hz (by omega) hleft hzA)
      · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
          (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hz (by omega) (by omega)
        refine Or.inr (Or.inr (Or.inr ⟨kc+1-i,by omega,by omega,?_⟩))
        rcases he with he | he
        · exact Or.inl (he.trans (hreverse i hin).1.symm)
        · exact Or.inr (he.trans (hreverse i hin).2.symm)
  obtain ⟨r,hC⟩ := capPrefixData_of_region M hM hH T hd
    ⟨hsel 10 (by exact Or.inr (Or.inr rfl)),hsel 8 (Or.inl rfl),hsel 9 (Or.inr (Or.inl rfl))⟩
    (habs 0 (by decide)) (habs 3 (by decide)) hregion
  exact ⟨kc+1,r,hC⟩

end WaveTurbulence.Vine
