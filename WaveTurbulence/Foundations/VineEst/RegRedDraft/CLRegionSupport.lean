/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLExternalSlots
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairAtSides

/-! # Exact node, branch and leaf-pair supports of the actual CL realization -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

noncomputable def clRealizationNodes {w : ℕ} (G : Garden w) (U : Finset (GBranch G.tree)) :
    Finset (GNode G.tree) := by
  classical
  exact Finset.univ.filter (Mole.InIncidenceRealization G U)

noncomputable def clBoundaryNodes {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) : Fin 4 → GNode G.tree :=
  ![a.toNode,a.child R.excluded,b.child R.positive,b.child R.negative]

noncomputable def clLocalSupport {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) : Finset (GNode G.tree) :=
  clRealizationNodes G U ∪ Finset.univ.image (clBoundaryNodes R)

noncomputable def clInteriorNodes {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (_R : CLRegionData G U a b) : Finset (GNode G.tree) :=
  (clRealizationNodes G U).erase a.toNode

noncomputable def clInteriorBranches {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (_R : CLRegionData G U a b) : Finset (GBranch G.tree) := U.erase a

noncomputable def clRegionalPairs {w : ℕ} {G : Garden w} (hG : G.IsPlain)
    (U : Finset (GBranch G.tree)) : Finset (SourcePair G) :=
  by
    classical
    exact Finset.univ.filter (fun p => Mole.IsInternalLeaf G U (p.firstLeaf hG))

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem mem_clRealizationNodes (x : GNode G.tree) :
    x ∈ clRealizationNodes G U ↔ Mole.InIncidenceRealization G U x := by
  classical
  simp only [clRealizationNodes,Finset.mem_filter,Finset.mem_univ,true_and]

theorem branch_mem_clRealizationNodes (v : GBranch G.tree) :
    v.toNode ∈ clRealizationNodes G U ↔ v ∈ U :=
  (mem_clRealizationNodes v.toNode).trans (Mole.branch_incidence_realization_iff G U v)

theorem leaf_mem_clRealizationNodes (ℓ : GLeaf G.tree) :
    ℓ.toNode ∈ clRealizationNodes G U ↔ Mole.IsInternalLeaf G U ℓ :=
  (mem_clRealizationNodes ℓ.toNode).trans (Mole.leaf_incidence_realization_iff G U ℓ)

theorem clBoundaryNodes_mem_support (R : CLRegionData G U a b) (j : Fin 4) :
    clBoundaryNodes R j ∈ clLocalSupport R :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

theorem cl_realization_mem_support (R : CLRegionData G U a b) {x : GNode G.tree}
    (hx : x ∈ clRealizationNodes G U) : x ∈ clLocalSupport R := Finset.mem_union_left _ hx

theorem cl_child_mem_realization_of_internal (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {v : GBranch G.tree} (hv : v ∈ U) (i : Fin 3) (hi : i.succ ∈ Mole.internalPositions G U v) :
    v.child i ∈ clRealizationNodes G U := by
  have hd := hU
  apply (mem_clRealizationNodes _).mpr
  apply (Mole.cl_node_realization_iff G hd R.parentPattern _).mpr
  exact Mole.cl_pruned_child_extension G ((Mole.cl_branch_realization_iff G hd R.parentPattern v).mp hv) i hi

theorem cl_child_mem_support (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {v : GBranch G.tree} (hv : v ∈ U) (i : Fin 3) : v.child i ∈ clLocalSupport R := by
  classical
  by_cases hi : i.succ ∈ Mole.internalPositions G U v
  · exact cl_realization_mem_support R (cl_child_mem_realization_of_internal hU R hv i hi)
  · by_cases ha : v = a
    · subst v
      have he : i = R.excluded := by simpa only [R.upper,not_not] using hi
      exact he ▸ clBoundaryNodes_mem_support R 1
    · by_cases hb : v = b
      · subst v
        have hn : i ≠ R.kept := fun he => hi ((R.lower i).mpr he)
        rcases (R.lower_excluded i).mp hn with rfl | rfl
        · exact clBoundaryNodes_mem_support R 2
        · exact clBoundaryNodes_mem_support R 3
      · have hd := hU.2.2.2.2.2.2.2.2.1 v hv ha hb
        have he : Mole.internalPositions G U v = Finset.univ :=
          Finset.eq_univ_of_card _ ((Mole.card_internalPositions G U v).trans hd)
        exact (hi (he ▸ Finset.mem_univ _)).elim

theorem cl_realization_parent (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (x : GNode G.tree) (hx : x ∈ clRealizationNodes G U) (hne : x ≠ a.toNode) :
    ∃ hn : x.1.2 ≠ [], x.parent hn ∈ U := by
  have hd := hU
  have hp := (Mole.cl_node_realization_iff G hd R.parentPattern x).mp ((mem_clRealizationNodes x).mp hx)
  have hn := Mole.pruned_node_nonroot G hp hne
  exact ⟨hn,(Mole.cl_branch_realization_iff G hd R.parentPattern _).mpr (Mole.pruned_parent G hp hne hn)⟩

end WaveTurbulence.RegRed
