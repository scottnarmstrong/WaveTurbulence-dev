/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.FinalCount.AtMapInl
public import WaveTurbulence.Foundations.FinalCount.AtMapGarden
public import WaveTurbulence.Foundations.FinalCount.AsmGeom
/-! **FINALCOUNT-ASSEMBLY (garden level, 2): `SubHyp` of the renamed molecule `inlMol G.molecule` and `TripleDesig` along `collMap`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCountG3 WaveTurbulence.AtomTransport WaveTurbulence.MoleProp

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D]

theorem sameComponent_mapAtoms (M : Molecule V D) (ι : V ↪ W) {a b : V} (h : M.SameComponent a b) :
    (mapAtoms M ι).SameComponent (ι a) (ι b) := by
  unfold Molecule.SameComponent at h ⊢
  induction h with
  | rel x y hxy =>
    obtain ⟨z, hz1, hz2⟩ := hxy
    exact Relation.EqvGen.rel _ _ ⟨z, by simp [hz1], by simp [hz2]⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem subHyp_mapAtoms {M : Molecule V D} (ι : V ↪ W) {R : ℕ} (h : SubHyp R M) : SubHyp R (mapAtoms M ι) where
  bounds := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    rw [mapAtoms_outdeg, mapAtoms_indeg]; exact h.bounds b hb
  deg3 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    rw [mapAtoms_deg]; exact h.deg3 b hb
  count := by
    rw [mapAtoms_bonds, mapAtoms_atoms, Finset.card_map]; exact h.count
  noloop := by
    intro x
    simp only [mapAtoms_atom, mapAtoms_mate, ne_eq, ι.injective.eq_iff]
    exact h.noloop x
  conn := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := (mem_mapAtoms_atoms M ι).1 ha
    obtain ⟨b', hb', rfl⟩ := (mem_mapAtoms_atoms M ι).1 hb
    exact sameComponent_mapAtoms M ι (h.conn a' ha' b' hb')
  one_le := h.one_le


section collmap
variable {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀}

theorem tripleDesig_collMap (ι : V ↪ W) {C : CollData M₀} (h : TripleDesig C) : TripleDesig (collMap ι C) := by
  intro a b ha hb hab h3
  obtain ⟨a', ha', rfl⟩ := (mem_mapAtoms_atoms M₀ ι).1 ha
  obtain ⟨b', hb', rfl⟩ := (mem_mapAtoms_atoms M₀ ι).1 hb
  rw [mapAtoms_bondsBetween] at h3
  obtain ⟨v, c, x, y, hvc, hv, h1, h2, hT, hx, hy⟩ := h a' b' ha' hb' (fun e => hab (by rw [e])) h3
  refine ⟨ι v, ι c, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hvc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left; exact ⟨by rw [e1], by rw [e2]⟩
    · right; exact ⟨by rw [e1], by rw [e2]⟩
  · rw [collMap_hinges]; exact Finset.mem_map_of_mem _ hv
  · rw [collMap_first]; exact h1
  · rw [collMap_second]; exact h2
  · exact (tripleAtM_iff ι v x y).2 hT
  · simp only [mapAtoms_atom, mapAtoms_mate]; rw [hx]
  · simp only [mapAtoms_atom, mapAtoms_mate]; rw [hy]

end collmap

end WaveTurbulence.FinalCountAsm
