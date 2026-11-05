/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperCoreProfiles
public import WaveTurbulence.Foundations.Molecule.VineHyperEmptySlots
public import WaveTurbulence.Foundations.Molecule.VineSideVIIData
public import WaveTurbulence.Foundations.Molecule.VineHyperPrefixSuffix
public import WaveTurbulence.Foundations.Molecule.VineCapPrefixData
import Mathlib.Tactic

/-! # The actual type-VII hyper-block region is a triangle and a cyan prefix -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every actual hyper-block subset of type VII has exactly the triangular
core and a prefix of its cyan ladder. All red/green fresh atoms are excluded
from the source incidence data, for arbitrary rung counts. -/
theorem typeVII_hyper_cap_region (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (R : VineRealization M .VII S a b)
    (hS : M.IsBlock S a b) (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    let c : Fin 11 → V := fun i => (R.coreAtom i).1
    ∃ kr kc kg r,R.k=[kr,kc,kg] ∧ r ≤ kc ∧
      ∃ D : SideLadderData M (c 4) (c 5) (c 6) (c 7) (c 8) kc,
        (∀ i,D.ladder.u i ∈ S ∧ D.ladder.v i ∈ S) ∧
        (∀ i,1 ≤ i → i ≤ kc → R.f (D.ladder.u i)=11+2*kr+(i-1) ∧
          R.f (D.ladder.v i)=11+2*kr+kc+(i-1)) ∧
        (univ : Finset (CapIndex r)).image
          (capAtomFamily (c 4) (c 5) (c 6) D.ladder.u D.ladder.v r)=A := by
  let c : Fin 11 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 11) : R.f (c i)=i.1 := R.label_coreAtom i
  have hlen : R.k.length=3 := R.length_eq
  obtain ⟨kr,kc,kg,hks⟩ := List.length_eq_three.mp hlen
  obtain ⟨W,hW,hprof⟩ := hyperBlock_core_profile M hM R hS hAS hH
  have hWeq : W=({4,5,6} : Finset ℕ) := by
    simpa only [hyperCoreSets,List.mem_cons,List.not_mem_nil,or_false] using hW
  subst W
  have hcore (z : V) (hz : z ∈ S) (hi : R.f z<11) :
      z ∈ A ↔ R.f z=4 ∨ R.f z=5 ∨ R.f z=6 := by
    simpa only [mem_insert,mem_singleton] using hprof z hz hi
  have hsel (i : Fin 11) (hi : i.1=4 ∨ i.1=5 ∨ i.1=6) : c i ∈ A := by
    apply (hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mpr
    rw [hlabelc]
    exact hi
  have h7 : c 7 ∉ A := by
    intro hz
    have hh := (hcore (c 7) (R.coreAtom (7 : Fin 11)).2 (by rw [hlabelc]; decide)).mp hz
    rw [hlabelc] at hh
    norm_num at hh
  have h8 : c 8 ∉ A := by
    intro hz
    have hh := (hcore (c 8) (R.coreAtom (8 : Fin 11)).2 (by rw [hlabelc]; decide)).mp hz
    rw [hlabelc] at hh
    norm_num at hh
  have hred := hyperBlock_empty_slot_from_ports M hM R hH []
    [(((5,7),(6,8)),kc),(((7,9),(8,10)),kg)] ((2,7),(3,8)) kr (by rw [hks]; rfl) (by
      intro z hz hl hzA
      dsimp only at hl
      have hi : R.f z<11 := by rcases hl with h | h | h | h <;> omega
      have hh := (hcore z hz hi).mp hzA
      omega)
  dsimp only [List.foldl_nil,VineType.template] at hred
  have hgreen := hyperBlock_empty_slot_from_ports M hM R hH
    [(((2,7),(3,8)),kr),(((5,7),(6,8)),kc)] [] ((7,9),(8,10)) kg (by rw [hks]; rfl) (by
      intro z hz hl hzA
      dsimp only at hl
      have hi : R.f z<11 := by rcases hl with h | h | h | h <;> omega
      have hh := (hcore z hz hi).mp hzA
      omega)
  simp only [List.foldl_cons,List.foldl_nil,insertRungs_atoms,VineType.template] at hgreen
  obtain ⟨D,hmem,hlabels⟩ := typeVII_side_data M R kr kc kg hks
  have huN : D.ladder.u (kc+1) ∉ A := by simpa only [D.end_upper] using h7
  have hvN : D.ladder.v (kc+1) ∉ A := by simpa only [D.end_lower] using h8
  obtain ⟨r,hr,hprefix⟩ := hyperBlock_sequence_prefix M hM hH D.ladder huN hvN
  have hregion : ∀ z ∈ A,z=c 4 ∨ z=c 5 ∨ z=c 6 ∨
      ∃ i,1 ≤ i ∧ i ≤ r ∧ (z=D.ladder.u i ∨ z=D.ladder.v i) := by
    intro z hzA
    have hz := hAS hzA
    have hzn := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hz)
    rw [hks,expand_atoms_exact .VII [kr,kc,kg] rfl] at hzn
    simp only [VineType.template,List.sum_cons,List.sum_nil,Nat.add_zero] at hzn
    by_cases hold : R.f z<11
    · rcases (hcore z hz hold).mp hzA with h | h | h
      · exact Or.inl (R.injOn hz (R.coreAtom (4 : Fin 11)).2 (h.trans (hlabelc 4).symm))
      · exact Or.inr (Or.inl (R.injOn hz (R.coreAtom (5 : Fin 11)).2 (h.trans (hlabelc 5).symm)))
      · exact Or.inr (Or.inr (Or.inl (R.injOn hz (R.coreAtom (6 : Fin 11)).2 (h.trans (hlabelc 6).symm))))
    · by_cases hleft : R.f z<11+2*kr
      · exact False.elim (hred z hz (by omega) hleft hzA)
      · by_cases hcyan : R.f z<11+2*kr+2*kc
        · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn D.ladder
            (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hz (by omega) hcyan
          have hir : i ≤ r := by
            apply (hprefix i hi hin).mp
            rcases he with he | he
            · exact he ▸ hzA
            · exact (hyperBlock_sequence_pair_membership M hM hH D.ladder i hi hin).mpr (he ▸ hzA)
          exact Or.inr (Or.inr (Or.inr ⟨i,hi,hir,he⟩))
        · exact False.elim (hgreen z hz (by omega) (by omega) hzA)
  refine ⟨kr,kc,kg,r,hks,hr,D,hmem,hlabels,?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hz
    cases i with
    | inl i =>
      fin_cases i
      · exact hsel 4 (by exact Or.inl rfl)
      · exact hsel 5 (by exact Or.inr (Or.inl rfl))
      · exact hsel 6 (by exact Or.inr (Or.inr rfl))
    | inr i =>
      cases i with
      | inl i => exact (hprefix (i.1+1) (by omega) (by omega)).mpr (by omega)
      | inr i =>
        apply (hyperBlock_sequence_pair_membership M hM hH D.ladder (i.1+1) (by omega) (by omega)).mp
        exact (hprefix (i.1+1) (by omega) (by omega)).mpr (by omega)
  · intro hz
    rcases hregion z hz with h | h | h | ⟨i,hi,hir,he⟩
    · exact mem_image.mpr ⟨.inl 0,mem_univ _,h.symm⟩
    · exact mem_image.mpr ⟨.inl 1,mem_univ _,h.symm⟩
    · exact mem_image.mpr ⟨.inl 2,mem_univ _,h.symm⟩
    · rcases he with he | he
      · refine mem_image.mpr ⟨.inr (.inl ⟨i-1,by omega⟩),mem_univ _,?_⟩
        change D.ladder.u (i-1+1)=z
        rw [show i-1+1=i by omega]
        exact he.symm
      · refine mem_image.mpr ⟨.inr (.inr ⟨i-1,by omega⟩),mem_univ _,?_⟩
        change D.ladder.v (i-1+1)=z
        rw [show i-1+1=i by omega]
        exact he.symm

end WaveTurbulence.Vine
