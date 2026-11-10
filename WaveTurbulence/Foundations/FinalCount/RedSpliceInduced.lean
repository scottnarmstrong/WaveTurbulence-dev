/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): isomorphic induced subgraphs transport blocks and vines

`InducedIso M M' B B'` is an isomorphism between the atomic group `B` of `M` (with the darts internal to
`B`) and the atomic group `B'` of `M'`.  Blocks and vines transport along such an isomorphism.  It is
used for the residual vines of the spliced garden, where `B'` contains merged atoms.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence

variable {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']

/-- An isomorphism of induced subgraphs. -/
structure InducedIso (M : Molecule V D) (M' : Molecule V' D') (B : Finset V) (B' : Finset V') where
  π : V → V'
  inj : Set.InjOn π B
  img : B.image π = B'
  sub : B' ⊆ M'.atoms
  e : {x : D // M.InGroup B x} ≃ {y : D' // M'.InGroup B' y}
  atom_comm : ∀ x, M'.atom (e x).1 = π (M.atom x.1)
  mate_comm : ∀ x, (e ⟨M.mate x.1, ⟨x.2.2, by simpa [M.mate_mate] using x.2.1⟩⟩).1 = M'.mate (e x).1
  out_comm : ∀ x, M'.out (e x).1 = M.out x.1

namespace InducedIso
variable {M : Molecule V D} {M' : Molecule V' D'} {B : Finset V} {B' : Finset V'} (I : InducedIso M M' B B')

theorem mem_B' {v' : V'} : v' ∈ B' ↔ ∃ v ∈ B, I.π v = v' := by
  have := Finset.ext_iff.mp I.img v'
  rw [Finset.mem_image] at this
  exact this.symm

theorem pi_mem {v : V} (hv : v ∈ B) : I.π v ∈ B' := (I.mem_B').mpr ⟨v, hv, rfl⟩

theorem card_filter (P : Bool → Prop) [DecidablePred P] {v : V} (hv : v ∈ B) :
    ((M'.dartsAt (I.π v)).filter (fun y => M'.InGroup B' y ∧ P (M'.out y))).card =
      ((M.dartsAt v).filter (fun x => M.InGroup B x ∧ P (M.out x))).card := by
  classical
  apply Finset.card_bij (fun y hy => (I.e.symm ⟨y, (Finset.mem_filter.mp hy).2.1⟩).1)
  · intro y hy
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hy
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    have hx := I.atom_comm (I.e.symm ⟨y, h2⟩)
    rw [Equiv.apply_symm_apply] at hx
    have hxB := (I.e.symm ⟨y, h2⟩).2.1
    have : M.atom (I.e.symm ⟨y, h2⟩).1 = v := I.inj hxB hv (by rw [← hx]; exact h1)
    refine Finset.mem_filter.mpr ⟨?_, (I.e.symm ⟨y, h2⟩).2, ?_⟩
    · simpa [Molecule.dartsAt] using this
    · have := I.out_comm (I.e.symm ⟨y, h2⟩)
      rw [Equiv.apply_symm_apply] at this
      rw [← this]; exact h3
  · intro y1 y2 hy1 hy2 h
    have h' := I.e.symm.injective (Subtype.ext h)
    exact congrArg Subtype.val h'
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hx
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    refine ⟨(I.e ⟨x, h2⟩).1, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, (I.e ⟨x, h2⟩).2, ?_⟩
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [I.atom_comm ⟨x, h2⟩]; simp [h1]
      · rw [I.out_comm ⟨x, h2⟩]; exact h3
    · simp

theorem isBlock {a b : V} (hB : M.IsBlock B a b) : M'.IsBlock B' (I.π a) (I.π b) := by
  obtain ⟨hsub, ha, hb, hab, h1, h2, h3, h4, h5, h6⟩ := hB
  refine ⟨I.sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact I.pi_mem ha
  · exact I.pi_mem hb
  · intro h; exact hab (I.inj ha hb h)
  · exact (I.card_filter (fun q => q = true) ha).trans h1
  · exact (I.card_filter (fun q => q = false) ha).trans h2
  · exact (I.card_filter (fun q => q = true) hb).trans h3
  · exact (I.card_filter (fun q => q = false) hb).trans h4
  · intro v' hv' hva hvb
    obtain ⟨v, hv, rfl⟩ := (I.mem_B').mp hv'
    have := I.card_filter (fun _ => True) hv
    simp only [and_true] at this
    unfold Molecule.degIn
    rw [this]
    exact h5 v hv (fun h => hva (h ▸ rfl)) (fun h => hvb (h ▸ rfl))
  · intro u' hu' v' hv'
    obtain ⟨u, hu, rfl⟩ := (I.mem_B').mp hu'
    obtain ⟨v, hv, rfl⟩ := (I.mem_B').mp hv'
    have hp := h6 u hu v hv
    clear hu hv hu' hv'
    induction hp with
    | rel a b hab =>
      obtain ⟨x, hx, hxa, hxb⟩ := hab
      apply Relation.EqvGen.rel
      refine ⟨(I.e ⟨x, hx⟩).1, (I.e ⟨x, hx⟩).2, ?_, ?_⟩
      · rw [I.atom_comm ⟨x, hx⟩]; exact congrArg I.π hxa
      · rw [← I.mate_comm ⟨x, hx⟩, I.atom_comm]; exact congrArg I.π hxb
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem ends_comm (x : {x : D // M.InGroup B x}) :
    M'.ends (I.e x).1 = Sym2.map I.π (M.ends x.1) := by
  unfold Molecule.ends
  rw [I.atom_comm x, ← I.mate_comm x, I.atom_comm]
  rfl

theorem groupBonds_map : M'.groupBonds B' = (M.groupBonds B).map (Sym2.map I.π) := by
  classical
  unfold Molecule.groupBonds
  rw [Multiset.map_map]
  apply Multiset.map_eq_map_of_bij_of_nodup (f := M'.ends)
    (g := (Sym2.map I.π) ∘ M.ends) (Finset.nodup _) (Finset.nodup _)
    (fun y hy => (I.e.symm ⟨y, (Finset.mem_filter.mp hy).2.2⟩).1)
  · intro y hy
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, (I.e.symm ⟨y, h2⟩).2⟩
    have := I.out_comm (I.e.symm ⟨y, h2⟩)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]; exact h1
  · intro y1 y2 hy1 hy2 h
    exact congrArg Subtype.val (I.e.symm.injective (Subtype.ext h))
  · intro x hx
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hx
    refine ⟨(I.e ⟨x, h2⟩).1, ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, (I.e ⟨x, h2⟩).2⟩
    rw [I.out_comm ⟨x, h2⟩]; exact h1
  · intro y hy
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hy
    have := I.ends_comm (I.e.symm ⟨y, h2⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this

theorem mem_of_mem_groupBonds {s : Sym2 V} (hs : s ∈ M.groupBonds B) : ∀ v ∈ s, v ∈ B := by
  classical
  unfold Molecule.groupBonds at hs
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hs
  obtain ⟨-, -, h2⟩ := Finset.mem_filter.mp hx
  intro v hv
  unfold Molecule.ends at hv
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact h2.1
  · exact h2.2

theorem isVine {X : VineType} {a b : V} (hV : M.IsVine X B a b) : M'.IsVine X B' (I.π a) (I.π b) := by
  classical
  obtain ⟨hB, k, hk, f, hf, himage, hj, hbonds⟩ := hV
  let f' : V' → ℕ := fun c => if h : ∃ v ∈ B, I.π v = c then f h.choose else 0
  have key : ∀ v ∈ B, f' (I.π v) = f v := by
    intro v hv
    have h : ∃ v0 ∈ B, I.π v0 = I.π v := ⟨v, hv, rfl⟩
    simp only [f', h, ↓reduceDIte]
    exact congrArg f (I.inj h.choose_spec.1 hv h.choose_spec.2)
  refine ⟨I.isBlock hB, k, hk, f', ?_, ?_, ?_, ?_⟩
  · intro c1 hc1 c2 hc2 he
    obtain ⟨v1, hv1, rfl⟩ := (I.mem_B').mp hc1
    obtain ⟨v2, hv2, rfl⟩ := (I.mem_B').mp hc2
    rw [key v1 hv1, key v2 hv2] at he
    rw [hf hv1 hv2 he]
  · ext n
    rw [← himage]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨v, hv, rfl⟩ := (I.mem_B').mp hc
      exact ⟨v, hv, (key v hv).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨I.π v, I.pi_mem hv, key v hv⟩
  · rw [key a hB.2.1, key b hB.2.2.1]; exact hj
  · rw [I.groupBonds_map, Multiset.map_map, ← hbonds]
    apply Multiset.map_congr rfl
    intro s hs
    induction s using Sym2.ind with
    | h u v =>
      have hu : u ∈ B := mem_of_mem_groupBonds hs u (Sym2.mem_mk_left _ _)
      have hv : v ∈ B := mem_of_mem_groupBonds hs v (Sym2.mem_mk_right _ _)
      simp [Sym2.map_mk, key u hu, key v hv]

theorem e_eq_iff {e : D} (he : M.InGroup B e) (x : {x : D // M.InGroup B x}) :
    (I.e x).1 = (I.e ⟨e, he⟩).1 ↔ x.1 = e :=
  ⟨fun h => congrArg Subtype.val (I.e.injective (Subtype.ext h)), fun h => by
    have : x = ⟨e, he⟩ := Subtype.ext h
    rw [this]⟩

theorem e_mate_iff {e : D} (he : M.InGroup B e) (x : {x : D // M.InGroup B x}) :
    (I.e x).1 = M'.mate (I.e ⟨e, he⟩).1 ↔ x.1 = M.mate e := by
  have hm : M.InGroup B (M.mate e) := ⟨he.2, by simpa [M.mate_mate] using he.1⟩
  rw [← I.mate_comm ⟨e, he⟩]
  constructor
  · intro h
    exact congrArg Subtype.val (I.e.injective (Subtype.ext h))
  · intro h
    have : x = ⟨M.mate e, hm⟩ := Subtype.ext h
    rw [this]

end InducedIso

end WaveTurbulence.RedSplice
