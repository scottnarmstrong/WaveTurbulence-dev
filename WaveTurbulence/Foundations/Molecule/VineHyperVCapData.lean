/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideVData
public import WaveTurbulence.Foundations.Molecule.VineHyperCoreProfiles
public import WaveTurbulence.Foundations.Molecule.VineCapPrefixConstruction
import Mathlib.Tactic

/-! # Source cap construction for every contained type-V hyper-block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, source cap construction in type V, including both
old doubled pairs and every inserted rung. No cap or prefix premise is used. -/
theorem typeV_hyper_cap_data (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} {a b x y : V} (hV : M.IsVine .V S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    ∃ n r,Nonempty (CapPrefixData M A n r) := by
  obtain ⟨hS,⟨R⟩⟩ := isVine_iff_realization.mp hV
  let c : Fin 9 → V := fun i => (R.coreAtom i).1
  have hlabelc (i : Fin 9) : R.f (c i)=i.1 := R.label_coreAtom i
  have hlen : R.k.length=1 := R.length_eq
  obtain ⟨k,hks⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨T,hd,Q,hmem,hports,hlabels,hreverse⟩ := typeV_side_data M R k hks
  obtain ⟨W,hW,hprof⟩ := hyperBlock_core_profile M hM R hS hAS hH
  have hw : W=({6,7,8} : Finset ℕ) ∨ W=({4,5,6,7,8} : Finset ℕ) ∨
      W=({2,3,4,5,6,7,8} : Finset ℕ) := by
    simpa only [hyperCoreSets,List.mem_cons,List.not_mem_nil,or_false] using hW
  have hwlo : ({6,7,8} : Finset ℕ) ⊆ W := by
    rcases hw with hw | hw | hw <;> subst W <;> decide
  have hwhi : W ⊆ ({2,3,4,5,6,7,8} : Finset ℕ) := by
    rcases hw with hw | hw | hw <;> subst W <;> decide
  have hcore (z : V) (hz : z ∈ S) (hi : R.f z<9) : z ∈ A ↔ R.f z ∈ W := hprof z hz hi
  have hsel (i : Fin 9) (hi : i.1=6 ∨ i.1=7 ∨ i.1=8) : c i ∈ A := by
    apply (hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mpr
    rw [hlabelc]
    apply hwlo
    simpa only [mem_insert,mem_singleton] using hi
  have habs (i : Fin 9) (hi : i.1<2) : c i ∉ A := by
    intro hz
    have hh := hwhi ((hcore (c i) (R.coreAtom i).2 (by rw [hlabelc]; exact i.2)).mp hz)
    rw [hlabelc] at hh
    simp only [mem_insert,mem_singleton] at hh
    omega
  have hregion : ∀ z ∈ A,z=c 8 ∨ z=c 6 ∨ z=c 7 ∨
      ∃ i,1 ≤ i ∧ i ≤ k+2 ∧ (z=T.ladder.u i ∨ z=T.ladder.v i) := by
    intro z hzA
    have hz := hAS hzA
    have hzn := mem_range.mp (R.image_eq ▸ mem_image_of_mem R.f hz)
    rw [hks,expand_atoms_exact .V [k] rfl] at hzn
    change R.f z<9+2*k at hzn
    have hzu (i : ℕ) (hi : i ≤ k+1) (hl : R.f z=R.f (Q.u i)) :
        z=T.ladder.u (k+2-i) := (R.injOn hz (hmem i).1 hl).trans (hreverse i hi).1.symm
    have hzv (i : ℕ) (hi : i ≤ k+1) (hl : R.f z=R.f (Q.v i)) :
        z=T.ladder.v (k+2-i) := (R.injOn hz (hmem i).2 hl).trans (hreverse i hi).2.symm
    by_cases hold : R.f z<9
    · have hh := hwhi ((hcore z hz hold).mp hzA)
      simp only [mem_insert,mem_singleton] at hh
      rcases hh with h | h | h | h | h | h | h
      · refine Or.inr (Or.inr (Or.inr ⟨k+2,by omega,le_rfl,Or.inl ?_⟩))
        exact hzu 0 (by omega) (h.trans (by rw [hports.1,hlabelc]; rfl))
      · refine Or.inr (Or.inr (Or.inr ⟨k+2,by omega,le_rfl,Or.inr ?_⟩))
        exact hzv 0 (by omega) (h.trans (by rw [hports.2.1,hlabelc]; rfl))
      · refine Or.inr (Or.inr (Or.inr ⟨1,le_rfl,by omega,Or.inl ?_⟩))
        have he := hzu (k+1) le_rfl (h.trans (by rw [hports.2.2.1,hlabelc]; rfl))
        simpa only [show k+2-(k+1)=1 by omega] using he
      · refine Or.inr (Or.inr (Or.inr ⟨1,le_rfl,by omega,Or.inr ?_⟩))
        have he := hzv (k+1) le_rfl (h.trans (by rw [hports.2.2.2,hlabelc]; rfl))
        simpa only [show k+2-(k+1)=1 by omega] using he
      · exact Or.inr (Or.inl (R.injOn hz (R.coreAtom (6 : Fin 9)).2 (h.trans (hlabelc 6).symm)))
      · exact Or.inr (Or.inr (Or.inl (R.injOn hz (R.coreAtom (7 : Fin 9)).2 (h.trans (hlabelc 7).symm))))
      · exact Or.inl (R.injOn hz (R.coreAtom (8 : Fin 9)).2 (h.trans (hlabelc 8).symm))
    · obtain ⟨i,hi,hin,he⟩ := allocatedSequence_covers M S R.f R.injOn Q
        (fun i hi hin => ⟨(hmem i).1,(hmem i).2,hlabels i hi hin⟩) hz (by omega) hzn
      refine Or.inr (Or.inr (Or.inr ⟨k+2-i,by omega,by omega,?_⟩))
      rcases he with he | he
      · exact Or.inl (he.trans (hreverse i (by omega)).1.symm)
      · exact Or.inr (he.trans (hreverse i (by omega)).2.symm)
  obtain ⟨r,hC⟩ := capPrefixData_of_region M hM hH T hd
    ⟨hsel 8 (Or.inr (Or.inr rfl)),hsel 6 (Or.inl rfl),hsel 7 (Or.inr (Or.inl rfl))⟩
    (habs 0 (by decide)) (habs 1 (by decide)) hregion
  exact ⟨k+2,r,hC⟩

end WaveTurbulence.Vine
