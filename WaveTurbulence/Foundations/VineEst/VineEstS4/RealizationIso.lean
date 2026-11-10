/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineCoherenceIndependent
public import WaveTurbulence.Foundations.Molecule.IsoVineTransport
public import WaveTurbulence.Foundations.Molecule.VineActualGroupSizes
public import WaveTurbulence.Foundations.Molecule.VineActualPartition

/-! # Realizations and cohmol groups under an actual garden isomorphism (V5 Step 4b, R31(2))

* `realization_iso`: a realization of a vine transported along an isomorphism of garden molecules.
* `realizedGroupSets_iso`: the group atom sets of the transported realization are the images of the original ones.
* `groups_of_corr`: for two chain pieces related by the isomorphism (same vine type, atoms, joints transported), the
  intrinsic cohmol group sets correspond (`realizedGroupSets_eq`).
* `realizedIncoherencyIndex_eq_card`: the incoherency index is the number of non-monochromatic group sets.
* `card_image_filter_nonmono`: it is unchanged when the atoms and the layering are transported along a bijection.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.Vine TTree
variable {w : ℕ}

section Realization
variable (G H : Garden w) (f : GardenDirectedIso G H)

/-- Realizations transport along an actual isomorphism of garden molecules. -/
theorem realization_iso {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : VineRealization G.molecule X S a b) :
    ∃ R' : VineRealization H.molecule X (isoAtoms G H f S) (f.branches a) (f.branches b),
      R'.k = R.k ∧ ∀ v, R'.f (f.branches v) = R.f v := by
  refine ⟨⟨R.k, R.length_eq, R.f ∘ f.branches.symm, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro u hu v hv he
    obtain ⟨u, rfl⟩ := f.branches.surjective u
    obtain ⟨v, rfl⟩ := f.branches.surjective v
    have he' : R.f u = R.f v := by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he
    exact congrArg f.branches (R.injOn ((mem_isoAtoms G H f S u).mp hu) ((mem_isoAtoms G H f S v).mp hv) he')
  · change (S.image f.branches).image (R.f ∘ f.branches.symm) = _
    rw [Finset.image_image]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using R.image_eq
  · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using R.joints_eq
  · rw [iso_groupBonds, Multiset.map_map]
    have he : (Sym2.map (R.f ∘ f.branches.symm)) ∘ Sym2.map f.branches = Sym2.map R.f := by
      funext p
      refine Sym2.inductionOn p ?_
      intro u v
      simp [Function.comp_def]
    rw [he]
    exact R.bonds_eq
  · intro v
    simp only [Function.comp_apply, Equiv.symm_apply_apply]

end Realization

section Groups

theorem mem_realizedGroupSets {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (s : Finset V) :
    s ∈ realizedGroupSets R ↔ ∃ g ∈ (X.expand R.k).groups, S.filter (fun v => R.f v ∈ g) = s := by
  unfold realizedGroupSets realizedGroups
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    ext v
    simp
  · rintro ⟨g, hg, rfl⟩
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    ext v
    simp

variable (G H : Garden w) (f : GardenDirectedIso G H)

theorem realizedGroupSets_iso {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : VineRealization G.molecule X S a b)
    (R' : VineRealization H.molecule X (isoAtoms G H f S) (f.branches a) (f.branches b))
    (hk : R'.k = R.k) (hf : ∀ v, R'.f (f.branches v) = R.f v) :
    realizedGroupSets R' = (realizedGroupSets R).image (Finset.image f.branches) := by
  classical
  ext s
  rw [mem_realizedGroupSets, Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [hk] at hg
    refine ⟨S.filter (fun v => R.f v ∈ g), (mem_realizedGroupSets R _).mpr ⟨g, hg, rfl⟩, ?_⟩
    ext v
    obtain ⟨u, rfl⟩ := f.branches.surjective v
    simp only [Finset.mem_image, Finset.mem_filter, mem_isoAtoms, hf]
    constructor
    · rintro ⟨x, ⟨hx, hg⟩, hxu⟩
      exact ⟨f.branches.injective hxu ▸ hx, f.branches.injective hxu ▸ hg⟩
    · rintro ⟨hx, hg⟩
      exact ⟨u, ⟨hx, hg⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (mem_realizedGroupSets R t).mp ht
    refine ⟨g, hk ▸ hg, ?_⟩
    ext v
    obtain ⟨u, rfl⟩ := f.branches.surjective v
    simp only [Finset.mem_image, Finset.mem_filter, mem_isoAtoms, hf]
    constructor
    · rintro ⟨hx, hg⟩
      exact ⟨u, ⟨hx, hg⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hg⟩, hxu⟩
      exact ⟨f.branches.injective hxu ▸ hx, f.branches.injective hxu ▸ hg⟩

/-- The cohmol groups of two chain pieces related by an isomorphism correspond. -/
theorem groups_of_corr {X Y : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {S' : Finset (GBranch H.tree)} {a' b' : GBranch H.tree}
    (R0 : VineRealization G.molecule X S a b) (R1 : VineRealization H.molecule Y S' a' b')
    (hS : S' = isoAtoms G H f S) (ha : a' = f.branches a) (hb : b' = f.branches b)
    (hB : G.molecule.IsBlock S a b) :
    realizedGroupSets R1 = (realizedGroupSets R0).image (Finset.image f.branches) := by
  subst hS ha hb
  obtain ⟨R', hk, hf⟩ := realization_iso G H f R0
  have hB' : H.molecule.IsBlock (isoAtoms G H f S) (f.branches a) (f.branches b) := iso_isBlock G H f hB
  rw [realizedGroupSets_eq H.molecule (Mole.garden_isMolecule H) R1 R' hB']
  exact realizedGroupSets_iso G H f R0 R' hk hf

end Groups

section Index
variable {V V' D : Type*} [DecidableEq V] [DecidableEq V'] [Fintype D]

/-- The incoherency index is the number of non-monochromatic group atom sets. -/
theorem realizedIncoherencyIndex_eq_card {L : Type*} [DecidableEq L] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) (layer : V → L) :
    realizedIncoherencyIndex R layer =
      ((realizedGroupSets R).filter (fun s => ¬∀ u ∈ s, ∀ v ∈ s, layer u = layer v)).card := by
  unfold realizedIncoherencyIndex
  rw [incoherencyIndex_as_groupSets]
  have hnd : ((realizedGroups R).map List.toFinset).Nodup := by
    apply groupSets_nodup (actual_groups_nodup R)
    intro g hg he
    have hh := realized_group_sizes R g hg
    rw [he] at hh
    simp only [List.length_nil] at hh
    omega
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext s
  simp [realizedGroupSets]

end Index

end WaveTurbulence.VineEstS4
