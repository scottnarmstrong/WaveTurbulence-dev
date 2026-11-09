/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproGap
public import WaveTurbulence.Foundations.FinalCount.SubproIso3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
import Mathlib.Tactic
/-! **L6-HRS hand port of main `WaveTurbulence.Foundations.FinalCount.SubproContained`** (sha256 in
`H/RS/COPIED-SHA256SUMS`; the porter did not emit it): main's text re-namespaced into `…FinalCount.H` with the
porter's carrier rewrites (`Object M` → `Src.Object Src.γL M`, `IsDV` → `Src.IsDV Src.γL`, …).

# SUBPRO (S4): TARGET `subpro` (4) (L2043--L2045), atom-set form

A vine-like object of `M_sb` that has no hinge atom and is not contained (by atoms) in an object of `C_1` is
contained (by atoms) in a DV or in an LG/ZG vine-like object, both disjoint from the hinges and from `C_1`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

theorem mem_objects' {σ : Prescription G} {O : Src.Object Src.γL (stSt G σ).G.molecule} (h : O ∈ objects G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ objOf G σ S = some O := by
  unfold objects at h
  obtain ⟨S, -, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2, -, -⟩ := objOf_spec hS
  exact ⟨S, h1, h2, hS⟩

theorem objOf_none (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (h : ¬ (G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S)) :
    objOf G σ S = none := by
  classical
  unfold objOf
  rw [dif_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)]

theorem objOf_some (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (hO : HasObj G S) :
    ∃ O, objOf G σ S = some O := by
  classical
  unfold objOf
  rw [dif_pos ⟨hM, hS, hσ, hO, not_markedGroup_empty G S, exists_obj hM σ hS hσ hO⟩]
  exact ⟨_, rfl⟩

theorem cover_group (hM : G.molecule.IsMolecule) {T : Finset (GBranch G.tree)} (hT : IsVineLikeSet G.molecule T) :
    ∃ g ∈ maximalGroups G.molecule, T ⊆ g := by
  have hpart := stage1Collection_isPartition hM
  obtain ⟨g, hg, hTg⟩ := cover_of_vineLike hpart hT
  exact ⟨g, by rw [← partition_eq_maximalGroups hpart]; exact hg, hTg⟩

theorem nohinge_unmerged (σ : Prescription G) {P : Finset (GBranch (stSt G σ).G.tree)}
    (hP : Disjoint P (stSt G σ).hinges) : ∀ c ∈ P, (stSt G σ).cls ((stSt G σ).M.ob c) = none := by
  intro c hc
  by_contra h
  exact Finset.disjoint_left.mp hP hc (((stSt G σ).mem_hinges c).mpr h)

theorem pi_ob (σ : Prescription G) {c : GBranch (stSt G σ).G.tree} (h : (stSt G σ).cls ((stSt G σ).M.ob c) = none) :
    (stSt G σ).M.pi (stSt G σ).hcls ((stSt G σ).M.ob c) = c := by
  apply (stSt G σ).M.ob_inj
  rw [(stSt G σ).M.ob_pi, repC_of_none h]

/-- Atoms of `M_sb` that are unmerged images of atoms of an object's group lie in the object. -/
theorem atoms_sub_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    {O : Src.Object Src.γL (stSt G σ).G.molecule} (hO : objOf G σ S = some O) {P : Finset (GBranch (stSt G σ).G.tree)}
    (hP : ∀ c ∈ P, (stSt G σ).M.ob c ∈ S ∧ (stSt G σ).cls ((stSt G σ).M.ob c) = none) : P ⊆ O.atoms := by
  obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO)
  obtain ⟨A, -, hOA, hnm, -⟩ := hSpec.src
  intro c hc
  obtain ⟨h1, h2⟩ := hP c hc
  rw [hOA]
  refine Finset.mem_image.mpr ⟨(stSt G σ).M.ob c, hnm _ h1 h2, pi_ob σ h2⟩

theorem obj_group_of_mem (σ : Prescription G) {O : Src.Object Src.γL (stSt G σ).G.molecule} (hO : O ∈ objects G σ) :
    ∃ S, G.molecule.IsMolecule ∧ S ∈ maximalGroups G.molecule ∧ objOf G σ S = some O :=
  mem_objects' hO


theorem mem_objects_of (σ : Prescription G) {S : Finset (GBranch G.tree)} {O : Src.Object Src.γL (stSt G σ).G.molecule}
    (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG) (hO : objOf G σ S = some O) :
    O ∈ objects G σ := by
  unfold objects
  exact List.mem_filterMap.mpr ⟨S, mem_sgGroups.mpr ⟨hS, hσ⟩, hO⟩

theorem containsDart_inGroup_SubproContained {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (O : Src.Object Src.γL M) {x : D} (h : O.ContainsDart x) : M.InGroup O.atoms x := by
  obtain ⟨A, a, b, sh⟩ := O
  cases sh with
  | vc _ => exact h
  | hyper _ => exact h.2.2

/-- The images of the unmerged atoms of a group are disjoint from the hinges. -/
theorem image_pi_disjoint_hinges (σ : Prescription G) {g : Finset (GBranch G.tree)}
    (hall : ∀ z0 ∈ g, (stSt G σ).cls z0 = none) :
    Disjoint (g.image ((stSt G σ).M.pi (stSt G σ).hcls)) (stSt G σ).hinges := by
  rw [Finset.disjoint_left]
  intro v hv hh
  obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.mp hv
  have := ((stSt G σ).mem_hinges _).mp hh
  rw [(stSt G σ).M.ob_pi, repC_of_none (hall z0 hz0)] at this
  exact this (hall z0 hz0)

/-- The image of a group without an object of `C_1` is disjoint from the objects of `C_1`. -/
theorem image_pi_disjoint_objects (hM : G.molecule.IsMolecule) (σ : Prescription G) {g : Finset (GBranch G.tree)}
    (hg : g ∈ maximalGroups G.molecule) (hall : ∀ z0 ∈ g, (stSt G σ).cls z0 = none)
    (hO : objOf G σ g = none) :
    ∀ O ∈ objects G σ, Disjoint (g.image ((stSt G σ).M.pi (stSt G σ).hcls)) O.atoms := by
  intro O hOm
  obtain ⟨S1, -, hS1, hO1⟩ := mem_objects' hOm
  obtain ⟨-, -, -, hSpec⟩ := objOf_spec (Option.mem_def.mpr hO1)
  rw [Finset.disjoint_left]
  intro v hv hvO
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z2, hz2, hz12⟩ := hSpec.atoms_sub _ hvO
  have e : repC (stSt G σ).cls z1 = repC (stSt G σ).cls z2 := by
    rw [← (stSt G σ).M.ob_pi (stSt G σ).hcls z1, ← (stSt G σ).M.ob_pi (stSt G σ).hcls z2, hz12]
  have h1 : repC (stSt G σ).cls z1 ∈ g := by rw [repC_of_none (hall z1 hz1)]; exact hz1
  have h2 : repC (stSt G σ).cls z2 ∈ S1 := repC_mem_group hM σ hS1 hz2
  have hgS : g = S1 := by
    by_contra hne
    exact Finset.disjoint_left.mp (groups_disjoint hM hg hS1 hne) h1 (e ▸ h2)
  rw [hgS] at hO
  rw [hO] at hO1
  cases hO1

end WaveTurbulence.GammaLow.FinalCount.H
