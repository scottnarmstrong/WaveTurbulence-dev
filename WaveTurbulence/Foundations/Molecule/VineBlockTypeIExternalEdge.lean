/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMixedSinglePaths
import Mathlib.Tactic

/-! # A surviving attachment outside one block and all double removals -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An actual edge outside one removed block survives when no type-I
piece contains both endpoints. This protects a normal center's remaining
doubled attachment; no single-edge premise is imposed. -/
theorem block_typeI_external_adj (M : Molecule V D) (S A : Finset V) (a b : V)
    (ps : List (RemovalPiece V D))
    (hI : ∀ P ∈ ps,M.IsVine .I P.atoms P.left P.right)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (huA : u ∉ A \ {a,b}) (hvA : v ∉ A \ {a,b})
    (hA : ¬(u ∈ A ∧ v ∈ A)) (hps : ∀ P ∈ ps,¬(u ∈ P.atoms ∧ v ∈ P.atoms))
    (ha : M.Adj u v) : (removeBlocks M S (blockRemoval M A a b::ps)).Adj u v := by
  classical
  obtain ⟨d,hdu,hdv⟩ := ha
  have hr := remainingAtoms_block_typeI M S A a b ps hI
  have hk : KeepDart M S (blockRemoval M A a b::ps) d := by
    refine ⟨hr.symm ▸ mem_sdiff.mpr ⟨hdu.symm ▸ hu,by simpa only [hdu] using huA⟩,
      hr.symm ▸ mem_sdiff.mpr ⟨hdv.symm ▸ hv,by simpa only [hdv] using hvA⟩,?_⟩
    intro P hP
    have hPd : P.darts=univ.filter (M.InGroup P.atoms) := by
      rcases List.mem_cons.mp hP with rfl | hP
      · rfl
      · exact hD P hP
    have hn : ¬M.InGroup P.atoms d := by
      intro hin
      rcases List.mem_cons.mp hP with rfl | hP
      · exact hA ⟨hdu ▸ hin.1,hdv ▸ hin.2⟩
      · exact hps P hP ⟨hdu ▸ hin.1,hdv ▸ hin.2⟩
    rw [hPd]
    constructor
    · simpa only [mem_filter,mem_univ,true_and] using hn
    · intro hm
      have hh := (mem_filter.mp hm).2
      exact hn ⟨by simpa only [M.mate_mate] using hh.2,hh.1⟩
  exact ⟨⟨d,hk⟩,hdu,hdv⟩

end WaveTurbulence.Vine
