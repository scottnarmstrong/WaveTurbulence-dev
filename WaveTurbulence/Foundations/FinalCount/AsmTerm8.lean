/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm7
public import WaveTurbulence.Foundations.FinalCount.G3ClFam2
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 8: the family of maximal connected clusters of a set `T` of atoms.**
`𝒦 = {cl a | a ∈ T}`, `cl a = {b ∈ T | b ~ a in the graph induced on T}`; `Clusters`, nonempty, inside the atoms and internally connected
(`FamData.int`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Connectivity in the graph induced on `T`. -/
def SCT (M : Molecule V D) (T : Finset V) : V → V → Prop :=
  Relation.EqvGen (fun u v => M.Adj u v ∧ u ∈ T ∧ v ∈ T)

/-- The cluster of `a`. -/
noncomputable def clOf (M : Molecule V D) (T : Finset V) (a : V) : Finset V := T.filter (fun b => SCT M T a b)

theorem adj_atoms {M : Molecule V D} {a b : V} (h : M.Adj a b) : a ∈ M.atoms ∧ b ∈ M.atoms := by
  obtain ⟨x, hx1, hx2⟩ := h
  exact ⟨hx1 ▸ M.atom_mem x, hx2 ▸ M.atom_mem _⟩

theorem eraseSet_compl_adj_iff (M : Molecule V D) (K : Finset V) {a b : V} :
    (eraseSet M (M.atoms \ K)).Adj a b ↔ M.Adj a b ∧ a ∈ K ∧ b ∈ K := by
  rw [eraseSet_adj_iff]
  constructor
  · rintro ⟨h, ha, hb⟩
    obtain ⟨ha', hb'⟩ := adj_atoms h
    refine ⟨h, ?_, ?_⟩
    · by_contra hn; exact ha (Finset.mem_sdiff.2 ⟨ha', hn⟩)
    · by_contra hn; exact hb (Finset.mem_sdiff.2 ⟨hb', hn⟩)
  · rintro ⟨h, ha, hb⟩
    exact ⟨h, fun h' => (Finset.mem_sdiff.1 h').2 ha, fun h' => (Finset.mem_sdiff.1 h').2 hb⟩

theorem SCT.symm' {M : Molecule V D} {T : Finset V} {x y : V} (h : SCT M T x y) : SCT M T y x :=
  Relation.EqvGen.symm _ _ h

theorem SCT.trans' {M : Molecule V D} {T : Finset V} {x y z : V} (h : SCT M T x y) (h' : SCT M T y z) : SCT M T x z :=
  Relation.EqvGen.trans _ _ _ h h'

theorem mem_clOf {M : Molecule V D} {T : Finset V} {a b : V} : b ∈ clOf M T a ↔ b ∈ T ∧ SCT M T a b := by
  unfold clOf; simp [Finset.mem_filter]

theorem clOf_eq_of_sct {M : Molecule V D} {T : Finset V} {a a' : V} (h : SCT M T a a') : clOf M T a = clOf M T a' := by
  ext b
  rw [mem_clOf, mem_clOf]
  constructor
  · rintro ⟨hb, hs⟩; exact ⟨hb, SCT.trans' (SCT.symm' h) hs⟩
  · rintro ⟨hb, hs⟩; exact ⟨hb, SCT.trans' h hs⟩

/-- Connectivity inside a cluster. -/
theorem cluster_int (M : Molecule V D) (T : Finset V) (a : V) :
    ∀ x y, SCT M T x y → ((x ∈ clOf M T a ↔ y ∈ clOf M T a) ∧
      (x ∈ clOf M T a → (eraseSet M (M.atoms \ clOf M T a)).SameComponent x y)) := by
  intro x y hxy
  induction hxy with
  | rel x y hr =>
    obtain ⟨hadj, hxT, hyT⟩ := hr
    have hs : SCT M T x y := Relation.EqvGen.rel _ _ ⟨hadj, hxT, hyT⟩
    have hiff : x ∈ clOf M T a ↔ y ∈ clOf M T a := by
      rw [mem_clOf, mem_clOf]
      constructor
      · rintro ⟨-, h⟩; exact ⟨hyT, SCT.trans' h hs⟩
      · rintro ⟨-, h⟩; exact ⟨hxT, SCT.trans' h (SCT.symm' hs)⟩
    refine ⟨hiff, fun hx => Relation.EqvGen.rel _ _ ((eraseSet_compl_adj_iff M _).2 ⟨hadj, hx, hiff.1 hx⟩)⟩
  | refl x => exact ⟨Iff.rfl, fun _ => Relation.EqvGen.refl _⟩
  | symm x y _ ih =>
    exact ⟨ih.1.symm, fun hy => Relation.EqvGen.symm _ _ (ih.2 (ih.1.2 hy))⟩
  | trans x y z _ _ ih1 ih2 =>
    refine ⟨ih1.1.trans ih2.1, fun hx => ?_⟩
    exact Relation.EqvGen.trans _ _ _ (ih1.2 hx) (ih2.2 (ih1.1.1 hx))

/-- **The cluster family of `T`.** -/
theorem exists_cluster_family (M : Molecule V D) (T : Finset V) (hT : T ⊆ M.atoms) :
    ∃ 𝒦 : Finset (Finset V), 𝒦.biUnion id = T ∧ Clusters M 𝒦 ∧
      (∀ K ∈ 𝒦, K.Nonempty ∧ K ⊆ M.atoms ∧ ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b) := by
  refine ⟨T.image (clOf M T), ?_, ⟨?_, ?_⟩, ?_⟩
  · ext b
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨K, ⟨a, ha, rfl⟩, hb⟩; exact (mem_clOf.1 hb).1
    · intro hb; exact ⟨clOf M T b, ⟨b, hb, rfl⟩, mem_clOf.2 ⟨hb, Relation.EqvGen.refl _⟩⟩
  · intro K hK K' hK' hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hK'
    rw [Finset.disjoint_left]
    intro b hb hb'
    exact hne (clOf_eq_of_sct (SCT.trans' (mem_clOf.1 hb).2 (SCT.symm' (mem_clOf.1 hb').2)))
  · intro K hK K' hK' hne x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hK'
    have hx1 := mem_clOf.1 hx
    have hx2 := mem_clOf.1 hx'
    have hadj : M.Adj (M.atom x) (M.atom (M.mate x)) := ⟨x, rfl, rfl⟩
    have hs : SCT M T (M.atom x) (M.atom (M.mate x)) := Relation.EqvGen.rel _ _ ⟨hadj, hx1.1, hx2.1⟩
    exact hne (clOf_eq_of_sct (SCT.trans' (SCT.trans' hx1.2 hs) (SCT.symm' hx2.2)))
  · intro K hK
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hK
    refine ⟨⟨a, mem_clOf.2 ⟨ha, Relation.EqvGen.refl _⟩⟩, fun b hb => hT (mem_clOf.1 hb).1, fun x hx y hy => ?_⟩
    exact (cluster_int M T a x y (SCT.trans' (SCT.symm' (mem_clOf.1 hx).2) (mem_clOf.1 hy).2)).2 hx

/-- **`FamData` for the cluster family of `T`.** -/
theorem exists_famData (M : Molecule V D) (T : Finset V) (hT : T ⊆ M.atoms) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hm4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hdpos : ∀ a ∈ T, 1 ≤ M.deg a) :
    ∃ 𝒦 : Finset (Finset V), 𝒦.biUnion id = T ∧ FamData M 𝒦 := by
  obtain ⟨𝒦, h1, h2, h3⟩ := exists_cluster_family M T hT
  refine ⟨𝒦, h1, ⟨h2, hnl, hm4, fun K hK => (h3 K hK).2.1, fun K hK => (h3 K hK).1, fun K hK a ha => ?_,
    fun K hK a ha b hb => (h3 K hK).2.2 a ha b hb⟩⟩
  refine hdpos a ?_
  rw [← h1]
  exact Finset.mem_biUnion.2 ⟨K, hK, ha⟩

end WaveTurbulence.FinalCountAsm
