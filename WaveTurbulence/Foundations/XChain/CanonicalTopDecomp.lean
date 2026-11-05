/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! Uniqueness of top construction data for the canonical reindexing in T.cmattr.
This file concerns a fixed garden; it does not claim the yet separate grafting/kernel identity. -/
public section
namespace WaveTurbulence.Induct
open Finset

/-- In a fixed garden, two valid top decompositions induce exactly the same partition. -/
theorem topDecomp_partition_unique {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (fl : Bool)
    (U : Finset (GNode LG.garden.tree)) (P Q : Finpartition U)
    (hP : LG.TopDecompWith fl p (LG.CanonInd p) LG.roots U P)
    (hQ : LG.TopDecompWith fl p (LG.CanonInd p) LG.roots U Q) : P = Q := by
  classical
  have hp := Canon.uniqueness p fl U P hP
  have hq := Canon.uniqueness p fl U Q hQ
  have hblock {B C : Finset (GNode LG.garden.tree)} (hB : B ∈ P.parts) (hC : C ∈ Q.parts)
      {u : GNode LG.garden.tree} (huB : u ∈ B) (huC : u ∈ C) : B = C := by
    ext v
    by_cases hv : v ∈ U
    · exact (hp.2 B hB u huB v hv).trans (hq.2 C hC u huC v hv).symm
    · exact iff_of_false (fun h => hv (P.le hB h)) (fun h => hv (Q.le hC h))
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hB
    have huU := P.le hB hu
    have he := hblock hB (Q.part_mem.mpr huU) hu (Q.mem_part huU)
    rw [he]
    exact Q.part_mem.mpr huU
  · intro hB
    obtain ⟨u, hu⟩ := Q.nonempty_of_mem_parts hB
    have huU := Q.le hB hu
    have he := hblock (P.part_mem.mpr huU) hB (P.mem_part huU) hu
    rw [← he]
    exact P.part_mem.mpr huU

/-- A canonical proper garden has exactly one top partition at its canonical attachment set. -/
theorem existsUnique_topDecomp {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hG : IsCanonG (p + 1) LG) :
    ∃! P : Finpartition (LG.attachNodes p),
      LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P := by
  have hi := (Canon.part1 p).mp hG
  have hTD := ((Canon.Rel.canonInd_succ (LG := LG)).mp hi.2).2.2.2.2
  obtain ⟨U, P, hP⟩ := Canon.Rel.unfold_topDecomp hTD
  have hU := (Canon.uniqueness p false U P hP).1
  subst U
  exact ⟨P, hP, fun Q hQ => topDecomp_partition_unique LG p false _ Q P hQ hP⟩

end WaveTurbulence.Induct
