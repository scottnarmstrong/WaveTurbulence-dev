/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceColl
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceColl2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a), B: `SubproChoices` of `G_sb`

`objects G σ`: the objects of `C_1`; `ProperPair`.  (R28: `hingePair`, `collectionChoices` and their theorems moved
to `RedSpliceHingePair`, after the designated pairs of `RedSpliceDesig`.)
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- The object of the SG group `S` in `G_sb` (if it contributes one). -/
@[expose] noncomputable def objOf (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree))
    (Mk : Set (CLVine G) := ∅) : Option (Src.Object Src.γL (stSt G σ Mk).G.molecule) := by
  classical
  exact if h : G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S ∧
      ¬ markedGroup G Mk S ∧ ∃ O : Src.Object Src.γL (stSt G σ Mk).G.molecule, ObjSpecMk G σ S Mk O then
    some (Classical.choose h.2.2.2.2.2) else none

/-- The objects of `C_1`.  B1a: with the marked vine set `Mk` (default `∅`), the objects of the unmarked SG groups
(o75: `𝒞₁` = main's objects restricted to `¬ markedGroup`). -/
@[expose] noncomputable def objects (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G) := ∅) :
    List (Src.Object Src.γL (stSt G σ Mk).G.molecule) :=
  (sgGroups G σ).filterMap (fun S => objOf G σ S Mk)

/-- B1b (Mk-general form of `objOf_spec`). -/
theorem objOf_specMk {σ : Prescription G} {S : Finset (GBranch G.tree)} {Mk : Set (CLVine _)} {O : Src.Object Src.γL (stSt (Mk := Mk) G σ).G.molecule}
    (h : O ∈ objOf (Mk := Mk) G σ S) :
    G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpecMk (Mk := Mk) G σ S O := by
  classical
  unfold objOf at h
  split_ifs at h with hh
  · rw [Option.mem_def, Option.some.injEq] at h
    subst h
    exact ⟨hh.1, hh.2.1, hh.2.2.1, Classical.choose_spec hh.2.2.2.2.2⟩
  · simp at h

theorem objOf_spec {σ : Prescription G} {S : Finset (GBranch G.tree)} {O : Src.Object Src.γL (stSt G σ).G.molecule}
    (h : O ∈ objOf G σ S) :
    G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpec G σ S O := objOf_specMk (Mk := ∅) h

/-- B1b (Mk-general form of `mem_objects`). -/
theorem mem_objectsMk {σ : Prescription G} {Mk : Set (CLVine _)} {O : Src.Object Src.γL (stSt (Mk := Mk) G σ).G.molecule} (h : O ∈ objects (Mk := Mk) G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpecMk (Mk := Mk) G σ S O := by
  unfold objects at h
  obtain ⟨S, _, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, h3, h4⟩ := objOf_specMk (Mk := Mk) hS
  exact ⟨S, h1, h2, h3, h4⟩

theorem mem_objects {σ : Prescription G} {O : Src.Object Src.γL (stSt G σ).G.molecule} (h : O ∈ objects G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ObjSpec G σ S O := mem_objectsMk (Mk := ∅) h

/-- B1b (Mk-general form of `objects_pairwise`). -/
theorem objects_pairwiseMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine _)} :
    (objects (Mk := Mk) G σ).Pairwise (fun O O' => Disjoint O.atoms O'.atoms) := by
  classical
  unfold objects
  rw [List.pairwise_filterMap]
  have hnd : (sgGroups G σ).Nodup := (Finset.nodup_toList _).filter _
  refine List.Pairwise.imp_of_mem ?_ hnd
  intro S T hS hT hne O hO O' hO'
  obtain ⟨_, hSm, _, hSpec⟩ := objOf_specMk (Mk := Mk) hO
  obtain ⟨_, hTm, _, hTpec⟩ := objOf_specMk (Mk := Mk) hO'
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨z, hz, rfl⟩ := hSpec.atoms_sub v hv
  obtain ⟨z', hz', hzz⟩ := hTpec.atoms_sub _ hv'
  have h1 := (stSt (Mk := Mk) G σ).M.ob_pi (stSt (Mk := Mk) G σ).hcls z
  have h2 := (stSt (Mk := Mk) G σ).M.ob_pi (stSt (Mk := Mk) G σ).hcls z'
  rw [← hzz] at h2
  have e : repC (stSt (Mk := Mk) G σ).cls z = repC (stSt (Mk := Mk) G σ).cls z' := h1.symm.trans h2
  exact Finset.disjoint_left.mp (groups_disjoint hM hSm hTm hne) (repC_mem_groupMk (Mk := Mk) hM σ hSm hz)
    (e ▸ repC_mem_groupMk (Mk := Mk) hM σ hTm hz')

theorem objects_pairwise (hM : G.molecule.IsMolecule) (σ : Prescription G) :
    (objects G σ).Pairwise (fun O O' => Disjoint O.atoms O'.atoms) := objects_pairwiseMk (Mk := ∅) hM σ

/-- A **proper hinge pair** at the hinge `v` is the lift of an external out/in pair of a unit (the unit whose crown
is `v`) at one of its joints (TARGET `subpro` (5): "the two bonds at one joint of `U` that do not belong to `U`"). -/
@[expose] def ProperPair (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)} (v : GBranch (stSt G σ Mk).G.tree)
    (x y : GardenDart (stSt G σ Mk).G) : Prop :=
  TripleAt (stSt G σ Mk).G v x y ∧ ∃ u ∈ unitBlocks G σ Mk, (stSt G σ Mk).M.ob v = u.upper ∧
    ∃ j, (j = u.upper ∨ j = u.lower) ∧ G.molecule.atom ((stSt G σ Mk).M.od x) = j ∧
      G.molecule.atom ((stSt G σ Mk).M.od y) = j ∧
      ¬ G.molecule.InGroup u.atoms ((stSt G σ Mk).M.od x) ∧ ¬ G.molecule.InGroup u.atoms ((stSt G σ Mk).M.od y)

end WaveTurbulence.GammaLow.FinalCount.H
