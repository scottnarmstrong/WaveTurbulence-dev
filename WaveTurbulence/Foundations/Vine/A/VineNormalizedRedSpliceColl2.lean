/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceColl
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
import Mathlib.Tactic

/-!
# R83 successor copy (source pinned/r83-RedSpliceColl2.lean; SHA in COPIED-SHA256SUMS).
# REDSPLICE-DEF (S2a), B: `SubproChoices` of `G_sb`

`objects G σ`: the objects of `C_1`; `ProperPair`.  (R28: `hingePair`, `collectionChoices` and their theorems moved
to `RedSpliceHingePair`, after the designated pairs of `RedSpliceDesig`.)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The object of the SG group `S` in `G_sb` (if it contributes one). -/
@[expose] noncomputable def objOf (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) :
    Option (Object (stSt G σ).G.molecule) := by
  classical
  exact if h : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S then
    some (Classical.choose (exists_obj h.1 σ h.2.1 h.2.2.1 h.2.2.2)) else none

/-- The objects of `C_1`. -/
@[expose] noncomputable def objects (G : Garden w) (σ : Prescription G) : List (Object (stSt G σ).G.molecule) :=
  (sgGroups G σ).filterMap (objOf G σ)

theorem objOf_spec {σ : Prescription G} {S : Finset (GBranch G.tree)} {O : Object (stSt G σ).G.molecule}
    (h : O ∈ objOf G σ S) :
    G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpec G σ S O := by
  classical
  unfold objOf at h
  split_ifs at h with hh
  · rw [Option.mem_def, Option.some.injEq] at h
    subst h
    exact ⟨hh.1, hh.2.1, hh.2.2.1, Classical.choose_spec (exists_obj hh.1 σ hh.2.1 hh.2.2.1 hh.2.2.2)⟩
  · simp at h

theorem mem_objects {σ : Prescription G} {O : Object (stSt G σ).G.molecule} (h : O ∈ objects G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpec G σ S O := by
  unfold objects at h
  obtain ⟨S, _, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, h3, h4⟩ := objOf_spec hS
  exact ⟨S, h1, h2, h3, h4⟩

theorem objects_pairwise (hM : G.molecule.IsMolecule) (σ : Prescription G) :
    (objects G σ).Pairwise (fun O O' => Disjoint O.atoms O'.atoms) := by
  classical
  unfold objects
  rw [List.pairwise_filterMap]
  have hnd : (sgGroups G σ).Nodup := (Finset.nodup_toList _).filter _
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro S T hS hT hne O hO O' hO'
  obtain ⟨_, hSm, _, hSpec⟩ := objOf_spec hO
  obtain ⟨_, hTm, _, hTpec⟩ := objOf_spec hO'
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨z, hz, rfl⟩ := hSpec.atoms_sub v hv
  obtain ⟨z', hz', hzz⟩ := hTpec.atoms_sub _ hv'
  have h1 := (stSt G σ).M.ob_pi (stSt G σ).hcls z
  have h2 := (stSt G σ).M.ob_pi (stSt G σ).hcls z'
  rw [← hzz] at h2
  have e : repC (stSt G σ).cls z = repC (stSt G σ).cls z' := h1.symm.trans h2
  exact Finset.disjoint_left.mp (groups_disjoint hM hSm hTm hne) (repC_mem_group hM σ hSm hz)
    (e ▸ repC_mem_group hM σ hTm hz')

/-- A **proper hinge pair** at the hinge `v` is the lift of an external out/in pair of a unit (the unit whose crown
is `v`) at one of its joints (TARGET `subpro` (5): "the two bonds at one joint of `U` that do not belong to `U`"). -/
@[expose] def ProperPair (G : Garden w) (σ : Prescription G) (v : GBranch (stSt G σ).G.tree)
    (x y : GardenDart (stSt G σ).G) : Prop :=
  TripleAt (stSt G σ).G v x y ∧ ∃ u ∈ unitBlocks G σ, (stSt G σ).M.ob v = u.upper ∧
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ).M.od x) = j ∧
      G.molecule.atom ((stSt G σ).M.od y) = j ∧
      ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od x) ∧ ¬ G.molecule.InGroup u.atoms ((stSt G σ).M.od y)

end WaveTurbulence.VineA.NormalizedSplice
