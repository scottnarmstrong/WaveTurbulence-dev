/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.Molecule.TwistSeparatedVines
public import WaveTurbulence.Foundations.Molecule.TwistCorePreservation
public import WaveTurbulence.Foundations.Molecule.TwistProtectedBranch
public import WaveTurbulence.Foundations.Molecule.TwistFiniteFamily
public import WaveTurbulence.Foundations.Molecule.TwistSpecialParents
public import WaveTurbulence.Foundations.Molecule.TwistParents
public import WaveTurbulence.Foundations.Molecule.ParentRegions
import Mathlib.Tactic

/-!
# The unit twist acts on the parent structure of (CL) vines

A *twist site* is the data of a unit twist: a core CL block `S0` (joints `a0`, `P.lower`) with its
designated placement.  For a vine atom set `T` that contains `S0` or meets it in at most one atom
(`TwistGood`), the parent incidence status of every atom of `T` is unchanged by the unit twist.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.Twist WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ}

/-- The data of a unit twist at a core (CL) block. -/
structure TwistSite (G : Garden w) where
  P : CorePlacement G
  S0 : Finset (GBranch G.tree)
  a0 : GBranch G.tree
  hB : G.molecule.IsBlock S0 a0 P.lower
  hCL : Mole.CLParentPattern G S0 a0 P.lower
  hP : IsPlacementAt G S0 P.lower P

namespace TwistSite
variable {G : Garden w} (Z : TwistSite G)

/-- The twisted garden. -/
@[expose, reducible] noncomputable def target : Garden w := unitTwistGarden G Z.P

/-- The molecule isomorphism of the unit twist. -/
@[expose] noncomputable def iso : MolIso G.molecule Z.target.molecule where
  e := coreBranchEquiv G Z.P
  d := twistDartEquiv G Z.P
  atoms_iff := fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  atom_comm := twistDartEquiv_atom G Z.P
  mate_comm := twistDartEquiv_mate G Z.P
  out_comm := twistDartEquiv_out G Z.P

/-- `T` contains the twisted block or meets it in at most one atom. -/
@[expose] def Good (T : Finset (GBranch G.tree)) : Prop :=
  Z.S0 ⊆ T ∨ SeparatedGroups Z.S0 T

/-- The old parent of the lower joint. -/
@[expose] noncomputable def pO : GBranch G.tree := GNode.parent Z.P.lower.toNode Z.P.nonroot
/-- The new parent of the lower joint (in the original coordinates). -/
@[expose] noncomputable def pN : GBranch G.tree :=
  GNode.parent (G.pair Z.P.retained).toNode Z.P.paired_nonroot

theorem pO_mem : Z.pO ∈ Z.S0 := by
  obtain ⟨h, hm⟩ := Z.hCL.2
  exact hm

theorem pN_mem : Z.pN ∈ Z.S0 := placement_paired_parent_mem G Z.P Z.hP

theorem pO_ne : Z.pO ≠ Z.P.lower := fun h => branch_ne_parent G Z.P.lower Z.P.nonroot h.symm

theorem pN_ne : Z.pN ≠ Z.P.lower := placement_paired_parent_ne G Z.P

theorem ip_map_ne {T : Finset (GBranch G.tree)} {v : GBranch G.tree} (hv : v ≠ Z.P.lower) :
    InternalParent Z.target (twistedAtoms G Z.P T) (coreBranchEquiv G Z.P v) ↔
      InternalParent G T v := by
  constructor
  · rintro ⟨h, hmem⟩
    have hn : v.1.2 ≠ [] := (coreBranchEquiv_nonroot G Z.P v).mp h
    refine ⟨hn, ?_⟩
    have := branchParent_transport G Z.P v hn hv
    have hmem' : GNode.parent (coreBranchEquiv G Z.P v).toNode
        ((coreBranchEquiv_nonroot G Z.P v).mpr hn) ∈ twistedAtoms G Z.P T := hmem
    rw [this] at hmem'
    exact (mem_twistedAtoms G Z.P T _).mp hmem'
  · rintro ⟨hn, hmem⟩
    refine ⟨(coreBranchEquiv_nonroot G Z.P v).mpr hn, ?_⟩
    change GNode.parent (coreBranchEquiv G Z.P v).toNode
        ((coreBranchEquiv_nonroot G Z.P v).mpr hn) ∈ twistedAtoms G Z.P T
    rw [branchParent_transport G Z.P v hn hv]
    exact (mem_twistedAtoms G Z.P T _).mpr hmem

theorem ip_old_lower {T : Finset (GBranch G.tree)} :
    InternalParent G T Z.P.lower ↔ Z.pO ∈ T :=
  ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨Z.P.nonroot, hm⟩⟩

theorem ip_new_lower {T : Finset (GBranch G.tree)} :
    InternalParent Z.target (twistedAtoms G Z.P T) (coreBranchEquiv G Z.P Z.P.lower) ↔
      Z.pN ∈ T := by
  constructor
  · rintro ⟨h, hm⟩
    have hm' : GNode.parent (coreBranchEquiv G Z.P Z.P.lower).toNode
        ((coreBranchEquiv_nonroot G Z.P Z.P.lower).mpr Z.P.nonroot) ∈ twistedAtoms G Z.P T := hm
    rw [lower_new_parent] at hm'
    exact (mem_twistedAtoms G Z.P T _).mp hm'
  · intro hm
    refine ⟨(coreBranchEquiv_nonroot G Z.P Z.P.lower).mpr Z.P.nonroot, ?_⟩
    change GNode.parent (coreBranchEquiv G Z.P Z.P.lower).toNode
        ((coreBranchEquiv_nonroot G Z.P Z.P.lower).mpr Z.P.nonroot) ∈ twistedAtoms G Z.P T
    rw [lower_new_parent]
    exact (mem_twistedAtoms G Z.P T _).mpr hm

/-- **Parent status is preserved** for good atom sets. -/
theorem ip_map {T : Finset (GBranch G.tree)} (hT : Z.Good T) {v : GBranch G.tree} (hv : v ∈ T) :
    InternalParent Z.target (twistedAtoms G Z.P T) (coreBranchEquiv G Z.P v) ↔
      InternalParent G T v := by
  by_cases hl : v = Z.P.lower
  · subst hl
    rw [Z.ip_new_lower, Z.ip_old_lower]
    rcases hT with hsub | hsep
    · exact ⟨fun _ => hsub Z.pO_mem, fun _ => hsub Z.pN_mem⟩
    · have h1 : Z.pO ∉ T := fun h =>
        Z.pO_ne (hsep _ Z.pO_mem h _ Z.hB.2.2.1 hv)
      have h2 : Z.pN ∉ T := fun h =>
        Z.pN_ne (hsep _ Z.pN_mem h _ Z.hB.2.2.1 hv)
      exact ⟨fun h => (h2 h).elim, fun h => (h1 h).elim⟩
  · exact Z.ip_map_ne hl

end TwistSite
end WaveTurbulence.Stage1
