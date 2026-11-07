/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundaryFullMultiplicity
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairPatterns
public import WaveTurbulence.Foundations.FinalCount.AppBStatistics
import Mathlib.Tactic

/-! # The source special-bond predicate constructs the actual double-tail figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Source 3R-2G's residual special bond supplies an actual 3S3New-3
realization. Its edge list is complete by the old degree-three stars. -/
theorem special_bond_realization (M : Molecule V D) (hno : AppbNoLoops M)
    {x : D} (hs : AppbSpecial M x) :
    ∃ r : AppbRealization M AppbPatternKind.s33new3.pattern,
      r.vertex 1 = M.atom x ∧ r.vertex 2 = M.atom (M.mate x) := by
  classical
  obtain ⟨ho,hdeg1,hdeg2,c,hc,d,hd,hcd,hca,hcb,hda,hdb,hcentral,hA,hB⟩ := hs
  have hne := hno x
  have hnd : ([M.atom x,M.atom (M.mate x),c,d] : List V).Nodup := by simp_all [ne_comm]
  have hmem : ∀ v ∈ ([M.atom x,M.atom (M.mate x),c,d] : List V),v ∈ M.atoms := by
    intro v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact M.atom_mem _
    · exact M.atom_mem _
    · exact hc
    · exact hd
  let data := singlePairEdges M hno hdeg1 hdeg2 hcentral
  have hl (i : Fin 2) : data.left.neighbor i = c :=
    data.left.neighbor_eq_of_full_multiplicity hcb hA i
  have hr (i : Fin 2) : data.right.neighbor i = d :=
    data.right.neighbor_eq_of_full_multiplicity hda hB i
  exact ⟨s33new3Realization M hne hnd hmem hdeg1 hdeg2 data (hl 0) (hl 1) (hr 0) (hr 1),rfl,rfl⟩

end WaveTurbulence.Mole.AppbAlgorithm
