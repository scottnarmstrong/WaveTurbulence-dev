/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVIData
public import WaveTurbulence.Foundations.Molecule.VineHyperCoreProfiles
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySlots
public import WaveTurbulence.Foundations.Molecule.VineCapPrefixConstruction
import Mathlib.Tactic

/-! # Source cap construction for every contained type-VI hyper-block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, source cap construction in type VIII. Old-core cut
classification and the actual slot incidences determine all cap-prefix data. -/
theorem typeVI_hyper_cap_data (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .VI S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ n r,Nonempty (CapPrefixData M A n r) := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  let c : Fin 15 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 15) : R.f (c i)=i.1 := R.label_coreAtom i
  have hlen : R.k.length=3 := R.length_eq
  obtain ⟨kr,kc,kg,hks⟩ := List.length_eq_three.mp hlen
  obtain ⟨T,hd,Q,hmem,hports,hlabels,hreverse⟩ := typeVI_side_data M R kr kc kg hks
  obtain ⟨W,hW,hprof⟩ := hyperBlock_core_profile M hM R hS hAS hH
  have hw : W=({10,11,12} : Finset ℕ) ∨ W=({8,9,10,11,12} : Finset ℕ) := by
    simpa only [hyperCoreSets,List.mem_cons,List.not_mem_nil,or_false] using hW
  have hwlo : ({10,11,12} : Finset ℕ) ⊆ W := by
    rcases hw with hw | hw <;> subst W <;> decide
  have hwhi : W ⊆ ({8,9,10,11,12} : Finset ℕ) := by
    rcases hw with hw | hw <;> subst W <;> decide
  have hcore (z : V) (hz : z ∈ S) (hi : R.f z<15) : z ∈ A ↔ R.f z ∈ W := hprof z hz hi
  have hsel (i : Fin 15) (hi : i.1=10 ∨ i.1=11 ∨ i.1=12) : c i ∈ A := by
    apply (hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mpr
    rw [hlabelc]
    apply hwlo
    simpa only [mem_insert,mem_singleton] using hi
  have habs (i : Fin 15) (hi : i.1 ≠ 8 ∧ i.1 ≠ 9 ∧ i.1 ≠ 10 ∧ i.1 ≠ 11 ∧ i.1 ≠ 12) : c i ∉ A := by
    intro hz
    have hh := hwhi ((hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mp hz)
    rw [hlabelc] at hh
    simp only [mem_insert,mem_singleton] at hh
    omega
  have hred := hyperBlock_empty_slot_from_ports M hM R hH []
    [(((8,10),(9,11)),kc),(((6,13),(7,14)),kg)] ((2,4),(3,5)) kr (by rw [hks]; rfl) (by
      intro z hz hl hzA
      dsimp only at hl
      have hi : R.f z<15 := by rcases hl with h | h | h | h <;> omega
      have hh := hwhi ((hcore z hz hi).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      omega)
  dsimp only [List.foldl_nil,VineType.template] at hred
  have hgreen := hyperBlock_empty_slot_from_ports M hM R hH
    [(((2,4),(3,5)),kr),(((8,10),(9,11)),kc)] [] ((6,13),(7,14)) kg (by rw [hks]; rfl) (by
      intro z hz hl hzA
      dsimp only at hl
      have hi : R.f z<15 := by rcases hl with h | h | h | h <;> omega
      have hh := hwhi ((hcore z hz hi).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      omega)
  simp only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] at hgreen
  have hregion : ∀ z ∈ A,z=c 12 ∨ z=c 10 ∨ z=c 11 ∨
      ∃ i,1 ≤ i ∧ i ≤ kc+1 ∧ (z=T.ladder.u i ∨ z=T.ladder.v i) := by
    intro z hzA
    have hz := hAS hzA
    have hzn := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hz)
    rw [hks,expand_atoms_exact .VI [kr,kc,kg] rfl] at hzn
    simp only [VineType.template,List.sum_cons,List.sum_nil,Nat.add_zero] at hzn
    by_cases hold : R.f z<15
    · have hh := hwhi ((hcore z hz hold).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h | h
      · have he : z=Q.u 0 := R.injOn hz (hmem 0).1 (h.trans (by rw [hports.1,hlabelc]; rfl))
        exact Or.inr (Or.inr (Or.inr ⟨kc+1,by omega,le_rfl,
          Or.inl (he.trans (hreverse 0 (by omega)).1.symm)⟩))
      · have he : z=Q.v 0 := R.injOn hz (hmem 0).2 (h.trans (by rw [hports.2.1,hlabelc]; rfl))
        exact Or.inr (Or.inr (Or.inr ⟨kc+1,by omega,le_rfl,
          Or.inr (he.trans (hreverse 0 (by omega)).2.symm)⟩))
      · exact Or.inr (Or.inl (R.injOn hz (R.coreAtom (10 : Fin 15)).2 (h.trans (hlabelc 10).symm)))
      · exact Or.inr (Or.inr (Or.inl (R.injOn hz (R.coreAtom (11 : Fin 15)).2 (h.trans (hlabelc 11).symm))))
      · exact Or.inl (R.injOn hz (R.coreAtom (12 : Fin 15)).2 (h.trans (hlabelc 12).symm))
    · by_cases hleft : R.f z<15+2*kr
      · exact False.elim (hred z hz (by omega) hleft hzA)
      · by_cases hcyan : R.f z<15+2*kr+2*kc
        · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
            (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hz (by omega) (by omega)
          refine Or.inr (Or.inr (Or.inr ⟨kc+1-i,by omega,by omega,?_⟩))
          rcases he with he | he
          · exact Or.inl (he.trans (hreverse i hin).1.symm)
          · exact Or.inr (he.trans (hreverse i hin).2.symm)
        · exact False.elim (hgreen z hz (by omega) (by omega) hzA)
  obtain ⟨r,hC⟩ := capPrefixData_of_region M hM hH T hd
    ⟨hsel 12 (by exact Or.inr (Or.inr rfl)),hsel 10 (Or.inl rfl),hsel 11 (Or.inr (Or.inl rfl))⟩
    (habs 5 (by decide)) (habs 7 (by decide)) hregion
  exact ⟨kc+1,r,hC⟩

end WaveTurbulence.Vine
