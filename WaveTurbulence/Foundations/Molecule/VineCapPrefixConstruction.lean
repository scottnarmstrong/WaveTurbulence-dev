/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixData
public import WaveTurbulence.Foundations.Molecule.VineHyperPrefixSuffix
import Mathlib.Tactic

/-! # Construct cap-prefix data from a contained hyper-block and primitive region data -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Incidence rows, a region cover and absent far ports determine the
selected cap prefix. The prefix and its atom-set identity are conclusions. -/
theorem capPrefixData_of_region (M : Molecule V D) (hM : M.IsMolecule)
    {A : Finset V} {x y center upper lower a b : V} {n : ℕ}
    (hH : Mole.IsHyperBlock M A x y) (D : SideLadderData M center upper lower a b n)
    (hd : Function.Injective (capAtomFamily center upper lower D.ladder.u D.ladder.v (n+1)))
    (ht : center ∈ A ∧ upper ∈ A ∧ lower ∈ A) (ha : a ∉ A) (hb : b ∉ A)
    (hregion : ∀ z ∈ A,z=center ∨ z=upper ∨ z=lower ∨
      ∃ i,1 ≤ i ∧ i ≤ n ∧ (z=D.ladder.u i ∨ z=D.ladder.v i)) :
    ∃ r,Nonempty (CapPrefixData M A n r) := by
  have huN : D.ladder.u (n+1) ∉ A := by simpa only [D.end_upper] using ha
  have hvN : D.ladder.v (n+1) ∉ A := by simpa only [D.end_lower] using hb
  obtain ⟨r,hr,hprefix⟩ := hyperBlock_sequence_prefix M hM hH D.ladder huN hvN
  refine ⟨r,⟨{
    center := center
    upper := upper
    lower := lower
    farUpper := a
    farLower := b
    side := D
    r_le := hr
    distinct := hd
    atoms_eq := ?_ }⟩⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hz
    rcases i with i | (i | i)
    · fin_cases i
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2
    · exact (hprefix (i.1+1) (by omega) (by omega)).mpr (by omega)
    · apply (hyperBlock_sequence_pair_membership M hM hH D.ladder (i.1+1) (by omega) (by omega)).mp
      exact (hprefix (i.1+1) (by omega) (by omega)).mpr (by omega)
  · intro hz
    rcases hregion z hz with he | he | he | ⟨i,hi,hin,he⟩
    · exact mem_image.mpr ⟨.inl 0,mem_univ _,he.symm⟩
    · exact mem_image.mpr ⟨.inl 1,mem_univ _,he.symm⟩
    · exact mem_image.mpr ⟨.inl 2,mem_univ _,he.symm⟩
    · have hir : i ≤ r := by
        apply (hprefix i hi hin).mp
        rcases he with he | he
        · exact he ▸ hz
        · exact (hyperBlock_sequence_pair_membership M hM hH D.ladder i hi hin).mpr (he ▸ hz)
      rcases he with he | he
      · refine mem_image.mpr ⟨.inr (.inl ⟨i-1,by omega⟩),mem_univ _,?_⟩
        change D.ladder.u (i-1+1)=z
        rw [show i-1+1=i by omega]
        exact he.symm
      · refine mem_image.mpr ⟨.inr (.inr ⟨i-1,by omega⟩),mem_univ _,?_⟩
        change D.ladder.v (i-1+1)=z
        rw [show i-1+1=i by omega]
        exact he.symm

end WaveTurbulence.Vine
