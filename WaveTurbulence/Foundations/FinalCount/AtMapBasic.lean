/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.MoleProp.AtomEmbedding
public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.Spine.SourceVineData
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 1: the block-level API of `mapAtoms M ι`

For an injective atom map `ι : V ↪ W`, `mapAtoms M ι : Molecule W D` has the same darts as `M`, so
decorations `κ : D → (Fin d → ℤ)` and admissibility predicates on them are literally shared.  This file proves
that the incidence data, atomic groups and `IsBlock` correspond along `S ↦ S.map ι`, and that every
block of `mapAtoms M ι` is the image of a block of `M` (transport in both directions). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp

variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) (ι : V ↪ W)

@[simp] theorem mapAtoms_atoms : (mapAtoms M ι).atoms = M.atoms.map ι := rfl
@[simp] theorem mapAtoms_atom (x : D) : (mapAtoms M ι).atom x = ι (M.atom x) := rfl
@[simp] theorem mapAtoms_mate (x : D) : (mapAtoms M ι).mate x = M.mate x := rfl
@[simp] theorem mapAtoms_out (x : D) : (mapAtoms M ι).out x = M.out x := rfl

theorem mem_mapAtoms_atoms {a : W} : a ∈ (mapAtoms M ι).atoms ↔ ∃ b ∈ M.atoms, ι b = a := by
  simp [Finset.mem_map]

theorem mapAtoms_deg (a : V) : (mapAtoms M ι).deg (ι a) = M.deg a := by
  simp only [Molecule.deg, mapAtoms_dartsAt]
theorem mapAtoms_outdeg (a : V) : (mapAtoms M ι).outdeg (ι a) = M.outdeg a := by
  simp only [Molecule.outdeg, mapAtoms_dartsAt]; rfl
theorem mapAtoms_indeg (a : V) : (mapAtoms M ι).indeg (ι a) = M.indeg a := by
  simp only [Molecule.indeg, mapAtoms_dartsAt]; rfl

theorem mapAtoms_bonds : (mapAtoms M ι).bonds = M.bonds := rfl

theorem mapAtoms_ends (x : D) : (mapAtoms M ι).ends x = Sym2.map ι (M.ends x) := rfl

theorem mapAtoms_ends_iff (x : D) (a b : V) :
    (mapAtoms M ι).ends x = s(ι a, ι b) ↔ M.ends x = s(a, b) := by
  rw [mapAtoms_ends, show s(ι a, ι b) = Sym2.map ι s(a, b) from rfl]
  exact (Sym2.map.injective ι.injective).eq_iff

theorem mapAtoms_bondsBetween (a b : V) :
    (mapAtoms M ι).bondsBetween (ι a) (ι b) = M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  congr 1
  ext x
  simp only [mem_filter, mapAtoms_bonds, mapAtoms_ends_iff]

theorem mapAtoms_directed (a b : V) : (mapAtoms M ι).Directed (ι a) (ι b) ↔ M.Directed a b := by
  unfold Molecule.Directed
  simp only [mapAtoms_out, mapAtoms_atom, mapAtoms_mate, ι.injective.eq_iff]

theorem mapAtoms_inGroup (S : Finset V) (x : D) :
    (mapAtoms M ι).InGroup (S.map ι) x ↔ M.InGroup S x := by
  simp [Molecule.InGroup]

theorem mapAtoms_degIn (S : Finset V) (a : V) :
    (mapAtoms M ι).degIn (S.map ι) (ι a) = M.degIn S a := by
  unfold Molecule.degIn
  simp only [mapAtoms_dartsAt]
  congr 1
  ext x; simp only [mem_filter, mapAtoms_inGroup]

theorem mapAtoms_outIn (S : Finset V) (a : V) :
    (mapAtoms M ι).outIn (S.map ι) (ι a) = M.outIn S a := by
  unfold Molecule.outIn
  simp only [mapAtoms_dartsAt]
  congr 1
  ext x; simp only [mem_filter, mapAtoms_inGroup]; rfl

theorem mapAtoms_inIn (S : Finset V) (a : V) :
    (mapAtoms M ι).inIn (S.map ι) (ι a) = M.inIn S a := by
  unfold Molecule.inIn
  simp only [mapAtoms_dartsAt]
  congr 1
  ext x; simp only [mem_filter, mapAtoms_inGroup]; rfl

theorem mapAtoms_groupBonds (S : Finset V) :
    (mapAtoms M ι).groupBonds (S.map ι) = (M.groupBonds S).map (Sym2.map ι) := by
  unfold Molecule.groupBonds
  rw [Multiset.map_map]
  congr 1
  congr 1
  ext x; simp only [mem_filter, mapAtoms_inGroup]; rfl

/-- `eraseBond` commutes with `mapAtoms` on the nose. -/
theorem mapAtoms_eraseBond (e : D) :
    (mapAtoms M ι).eraseBond e = mapAtoms (M.eraseBond e) ι := rfl

/-- Connectedness of an atomic group is preserved and reflected. -/
theorem mapAtoms_groupConnected (S : Finset V) :
    (mapAtoms M ι).GroupConnected (S.map ι) ↔ M.GroupConnected S := by
  unfold Molecule.GroupConnected
  constructor
  · intro h u hu v hv
    have key : ∀ a' b', Relation.EqvGen (fun a b => ∃ x, (mapAtoms M ι).InGroup (S.map ι) x ∧
        (mapAtoms M ι).atom x = a ∧ (mapAtoms M ι).atom ((mapAtoms M ι).mate x) = b) a' b' →
        a' = b' ∨ ∃ a b, a' = ι a ∧ b' = ι b ∧ Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧
          M.atom x = a ∧ M.atom (M.mate x) = b) a b := by
      intro a' b' hh
      induction hh with
      | rel a' b' hr =>
        obtain ⟨x, hx, ha, hb⟩ := hr
        right
        refine ⟨M.atom x, M.atom (M.mate x), ha.symm, hb.symm, Relation.EqvGen.rel _ _
          ⟨x, (mapAtoms_inGroup M ι S x).mp hx, rfl, rfl⟩⟩
      | refl a' => exact Or.inl rfl
      | symm a' b' _ ih =>
        rcases ih with h | ⟨a, b, h1, h2, h3⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨b, a, h2, h1, Relation.EqvGen.symm _ _ h3⟩
      | trans a' b' c' _ _ ih1 ih2 =>
        rcases ih1 with h | ⟨a, b, h1, h2, h3⟩
        · subst h; exact ih2
        · rcases ih2 with h' | ⟨b2, c, h1', h2', h3'⟩
          · subst h'; exact Or.inr ⟨a, b, h1, h2, h3⟩
          · have : b = b2 := ι.injective (h2.symm.trans h1')
            subst this
            exact Or.inr ⟨a, c, h1, h2', Relation.EqvGen.trans _ _ _ h3 h3'⟩
    rcases key _ _ (h (ι u) (Finset.mem_map' ι |>.mpr hu) (ι v) (Finset.mem_map' ι |>.mpr hv)) with
      h | ⟨a, b, h1, h2, h3⟩
    · rw [ι.injective h]; exact Relation.EqvGen.refl _
    · rw [ι.injective h1, ι.injective h2]; exact h3
  · intro h u' hu' v' hv'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    have key : ∀ a b, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧
        M.atom (M.mate x) = b) a b → Relation.EqvGen (fun a b => ∃ x, (mapAtoms M ι).InGroup (S.map ι) x ∧
        (mapAtoms M ι).atom x = a ∧ (mapAtoms M ι).atom ((mapAtoms M ι).mate x) = b) (ι a) (ι b) := by
      intro a b hh
      induction hh with
      | rel a b hr =>
        obtain ⟨x, hx, ha, hb⟩ := hr
        exact Relation.EqvGen.rel _ _ ⟨x, (mapAtoms_inGroup M ι S x).mpr hx, by simp [ha], by simp [hb]⟩
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    exact key _ _ (h u hu v hv)

/-- Every atomic group of `mapAtoms M ι` is the image of an atomic group of `M`. -/
theorem exists_map_of_subset {S' : Finset W} (h : S' ⊆ (mapAtoms M ι).atoms) :
    ∃ S ⊆ M.atoms, S' = S.map ι := Finset.subset_map_iff.mp h

theorem mapAtoms_isBlock (S : Finset V) (j₁ j₂ : V) :
    (mapAtoms M ι).IsBlock (S.map ι) (ι j₁) (ι j₂) ↔ M.IsBlock S j₁ j₂ := by
  unfold Molecule.IsBlock
  rw [mapAtoms_atoms, Finset.map_subset_map, Finset.mem_map' ι, Finset.mem_map' ι, ι.injective.ne_iff,
    mapAtoms_outIn, mapAtoms_inIn, mapAtoms_outIn, mapAtoms_inIn, mapAtoms_groupConnected]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro h v hv h1 h2
    have := h (ι v) ((Finset.mem_map' ι).mpr hv) (ι.injective.ne_iff.mpr h1) (ι.injective.ne_iff.mpr h2)
    rwa [mapAtoms_degIn] at this
  · intro h v' hv' h1 h2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
    rw [mapAtoms_degIn]
    exact h v hv (fun e => h1 (e ▸ rfl)) (fun e => h2 (e ▸ rfl))

/-- Every block of `mapAtoms M ι` is the image of a block of `M` (with images of its joints). -/
theorem exists_isBlock_of_mapAtoms {S' : Finset W} {a' b' : W} (h : (mapAtoms M ι).IsBlock S' a' b') :
    ∃ S a b, S' = S.map ι ∧ a' = ι a ∧ b' = ι b ∧ M.IsBlock S a b := by
  obtain ⟨S, -, rfl⟩ := exists_map_of_subset M ι h.1
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp h.2.1
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp h.2.2.1
  exact ⟨S, a, b, rfl, rfl, rfl, (mapAtoms_isBlock M ι S a b).mp h⟩

end WaveTurbulence.AtomTransport
