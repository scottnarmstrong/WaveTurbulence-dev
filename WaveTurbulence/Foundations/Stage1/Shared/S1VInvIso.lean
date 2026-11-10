/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Collection
public import WaveTurbulence.Foundations.Molecule.GardenDirectedIso
import Mathlib.Tactic

/-!
# Abstract molecule isomorphisms and transport of blocks and vines

A generic isomorphism of molecules `MolIso M N` (a bijection of atoms and of darts commuting with
`atom`, `mate`, `out`), and the transport of groups, degrees, blocks and vines.  This is the generic
form of `Twist.iso_isBlock`/`iso_isVine`, needed because the adjoint molecule `eraseBond M e` is not
a garden molecule.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V V' D D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']

/-- An isomorphism of molecules. -/
structure MolIso (M : Molecule V D) (N : Molecule V' D') where
  e : V ≃ V'
  d : D ≃ D'
  atoms_iff : ∀ v, e v ∈ N.atoms ↔ v ∈ M.atoms
  atom_comm : ∀ x, N.atom (d x) = e (M.atom x)
  mate_comm : ∀ x, N.mate (d x) = d (M.mate x)
  out_comm : ∀ x, N.out (d x) = M.out x

namespace MolIso
variable {M : Molecule V D} {N : Molecule V' D'} (F : MolIso M N)

/-- The image of an atom set. -/
@[expose] def img (S : Finset V) : Finset V' := S.image F.e

theorem mem_img (S : Finset V) (v : V) : F.e v ∈ F.img S ↔ v ∈ S := by
  unfold img
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
    exact F.e.injective he ▸ hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

theorem mem_img' (S : Finset V) (v' : V') : v' ∈ F.img S ↔ F.e.symm v' ∈ S := by
  rw [← F.mem_img S, Equiv.apply_symm_apply]

theorem img_injective : Function.Injective F.img := by
  intro S T h
  ext v
  rw [← F.mem_img S, ← F.mem_img T, h]

theorem img_subset_iff {S T : Finset V} : F.img S ⊆ F.img T ↔ S ⊆ T := by
  constructor
  · intro h v hv
    exact (F.mem_img T v).mp (h ((F.mem_img S v).mpr hv))
  · intro h v' hv'
    rw [F.mem_img'] at hv' ⊢
    exact h hv'

theorem img_union (S T : Finset V) : F.img (S ∪ T) = F.img S ∪ F.img T := by
  unfold img; exact Finset.image_union _ _

theorem img_inter (S T : Finset V) : F.img (S ∩ T) = F.img S ∩ F.img T := by
  unfold img; exact Finset.image_inter _ _ F.e.injective

theorem img_singleton (b : V) : F.img {b} = {F.e b} := by
  unfold img; exact Finset.image_singleton _ _


theorem inGroup_img (S : Finset V) (x : D) : N.InGroup (F.img S) (F.d x) ↔ M.InGroup S x := by
  have ha := F.atom_comm x
  have hb := (congrArg N.atom (F.mate_comm x)).trans (F.atom_comm (M.mate x))
  constructor
  · intro h
    exact ⟨(F.mem_img S _).mp (ha ▸ h.1), (F.mem_img S _).mp (hb ▸ h.2)⟩
  · intro h
    exact ⟨ha.symm ▸ (F.mem_img S _).mpr h.1, hb.symm ▸ (F.mem_img S _).mpr h.2⟩

theorem filter_card (S : Finset V) (v : V) (p : Bool → Prop) [DecidablePred p] :
    ((N.dartsAt (F.e v)).filter (fun y => N.InGroup (F.img S) y ∧ p (N.out y))).card =
    ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ p (M.out x))).card := by
  symm
  apply card_bij (fun x _hx => F.d x)
  · intro x hx
    obtain ⟨hat, hgroup, hp⟩ := Finset.mem_filter.mp hx
    have ha := (Mole.mem_dartsAt M v x).mp hat
    exact Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt N _ _).mpr
      ((F.atom_comm x).trans (congrArg F.e ha)), (F.inGroup_img S x).mpr hgroup,
      (F.out_comm x).symm ▸ hp⟩
  · intro x _hx y _hy he
    exact F.d.injective he
  · intro y hy
    obtain ⟨x, rfl⟩ := F.d.surjective y
    obtain ⟨hat, hgroup, hp⟩ := Finset.mem_filter.mp hy
    have hat := (Mole.mem_dartsAt N _ _).mp hat
    have ha := F.e.injective ((F.atom_comm x).symm.trans hat)
    exact ⟨x, Finset.mem_filter.mpr ⟨(Mole.mem_dartsAt M v x).mpr ha,
      (F.inGroup_img S x).mp hgroup, (F.out_comm x) ▸ hp⟩, rfl⟩

theorem degIn_img (S : Finset V) (v : V) : N.degIn (F.img S) (F.e v) = M.degIn S v := by
  simpa only [Molecule.degIn, and_true] using F.filter_card S v (fun _ => True)

theorem outIn_img (S : Finset V) (v : V) : N.outIn (F.img S) (F.e v) = M.outIn S v :=
  F.filter_card S v (fun b => b = true)

theorem inIn_img (S : Finset V) (v : V) : N.inIn (F.img S) (F.e v) = M.inIn S v :=
  F.filter_card S v (fun b => b = false)

theorem groupConnected_img {S : Finset V} (h : M.GroupConnected S) :
    N.GroupConnected (F.img S) := by
  intro u hu v hv
  obtain ⟨u, rfl⟩ := F.e.surjective u
  obtain ⟨v, rfl⟩ := F.e.surjective v
  have hp := h u ((F.mem_img S u).mp hu) v ((F.mem_img S v).mp hv)
  clear hu hv h
  induction hp with
  | rel a b hab =>
    obtain ⟨x, hx, ha, hb⟩ := hab
    apply Relation.EqvGen.rel
    refine ⟨F.d x, (F.inGroup_img S x).mpr hx, ?_, ?_⟩
    · rw [F.atom_comm, ha]
    · rw [F.mate_comm, F.atom_comm, hb]
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact Relation.EqvGen.trans _ _ _ hab hbc

theorem isBlock_img {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    N.IsBlock (F.img S) (F.e a) (F.e b) := by
  obtain ⟨hsub, ha, hb, hab, h1, h2, h3, h4, h5, h6⟩ := hB
  refine ⟨?_, (F.mem_img S a).mpr ha, (F.mem_img S b).mpr hb, F.e.injective.ne hab,
    ?_, ?_, ?_, ?_, ?_, F.groupConnected_img h6⟩
  · intro v' hv'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hv'
    exact (F.atoms_iff v).mpr (hsub hv)
  · rw [F.outIn_img]; exact h1
  · rw [F.inIn_img]; exact h2
  · rw [F.outIn_img]; exact h3
  · rw [F.inIn_img]; exact h4
  · intro v' hv hva hvb
    obtain ⟨v, rfl⟩ := F.e.surjective v'
    rw [F.degIn_img]
    exact h5 v ((F.mem_img S v).mp hv) (fun he => hva (congrArg F.e he))
      (fun he => hvb (congrArg F.e he))

theorem ends_comm (x : D) : N.ends (F.d x) = Sym2.map F.e (M.ends x) := by
  change s(N.atom (F.d x), N.atom (N.mate (F.d x))) = s(F.e (M.atom x), F.e (M.atom (M.mate x)))
  rw [F.atom_comm, F.mate_comm, F.atom_comm]

theorem groupBonds_img (S : Finset V) :
    N.groupBonds (F.img S) = (M.groupBonds S).map (Sym2.map F.e) := by
  have hset : (univ.filter fun x => N.out x = true ∧ N.InGroup (F.img S) x) =
      (univ.filter fun x => M.out x = true ∧ M.InGroup S x).image F.d := by
    ext y
    obtain ⟨x, rfl⟩ := F.d.surjective y
    constructor
    · intro h
      obtain ⟨_hu, ho, hg⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, F.out_comm x ▸ ho,
        (F.inGroup_img S x).mp hg⟩, rfl⟩
    · intro h
      obtain ⟨z, hz, he⟩ := mem_image.mp h
      have hzx := F.d.injective he
      subst z
      obtain ⟨_hu, ho, hg⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_univ _, (F.out_comm x).symm ▸ ho, (F.inGroup_img S x).mpr hg⟩
  unfold Molecule.groupBonds
  rw [hset, image_val_of_injOn F.d.injective.injOn, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _hx
  exact F.ends_comm x

theorem isVine_img {X : VineType} {S : Finset V} {a b : V} (hV : M.IsVine X S a b) :
    N.IsVine X (F.img S) (F.e a) (F.e b) := by
  obtain ⟨hB, k, hk, g, hg, himage, hj, hbonds⟩ := hV
  refine ⟨F.isBlock_img hB, k, hk, g ∘ F.e.symm, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv he
    obtain ⟨u, rfl⟩ := F.e.surjective u
    obtain ⟨v, rfl⟩ := F.e.surjective v
    have he' : g u = g v := by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he
    exact congrArg F.e (hg ((F.mem_img S u).mp hu) ((F.mem_img S v).mp hv) he')
  · change (S.image F.e).image (g ∘ F.e.symm) = _
    rw [Finset.image_image]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using himage
  · simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hj
  · rw [F.groupBonds_img, Multiset.map_map]
    have he : (Sym2.map (g ∘ F.e.symm)) ∘ Sym2.map F.e = Sym2.map g := by
      funext p
      refine Sym2.inductionOn p ?_
      intro u v
      simp [Function.comp_def]
    rw [he]
    exact hbonds

theorem isSomeVine_img {S : Finset V} {a b : V} (h : IsSomeVine M S a b) :
    IsSomeVine N (F.img S) (F.e a) (F.e b) :=
  let ⟨X, hX⟩ := h; ⟨X, F.isVine_img hX⟩

theorem chain_img {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    Chain N (F.img S) (F.e a) (F.e b) n := by
  induction h with
  | single hv => exact Chain.single (F.isSomeVine_img hv)
  | append _ hT hi hne ih =>
    rw [F.img_union]
    refine Chain.append ih (F.isSomeVine_img hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

/-- The inverse isomorphism. -/
@[expose] def symm : MolIso N M where
  e := F.e.symm
  d := F.d.symm
  atoms_iff := fun v' => by
    rw [← F.atoms_iff, Equiv.apply_symm_apply]
  atom_comm := fun y => by
    obtain ⟨x, rfl⟩ := F.d.surjective y
    rw [Equiv.symm_apply_apply, F.atom_comm, Equiv.symm_apply_apply]
  mate_comm := fun y => by
    obtain ⟨x, rfl⟩ := F.d.surjective y
    rw [Equiv.symm_apply_apply, F.mate_comm, Equiv.symm_apply_apply]
  out_comm := fun y => by
    obtain ⟨x, rfl⟩ := F.d.surjective y
    rw [Equiv.symm_apply_apply, F.out_comm]

/-- Deleting a bond commutes with the isomorphism. -/
@[expose] def erase (x : D) : MolIso (Molecule.eraseBond M x) (Molecule.eraseBond N (F.d x)) where
  e := F.e
  d := Equiv.subtypeEquiv F.d (fun y => by
    rw [F.mate_comm]
    exact and_congr F.d.injective.ne_iff.symm F.d.injective.ne_iff.symm)
  atoms_iff := F.atoms_iff
  atom_comm := fun y => F.atom_comm y.1
  mate_comm := fun y => Subtype.ext (F.mate_comm y.1)
  out_comm := fun y => F.out_comm y.1

theorem ends_img {x : D} {a b : V} (h : M.ends x = s(a, b)) : N.ends (F.d x) = s(F.e a, F.e b) := by
  rw [F.ends_comm, h]; rfl

theorem isDV_img {S : Finset V} {a b : V} (h : IsDV M S a b) :
    IsDV N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨A, B, hA, hB, hi, rfl⟩ := h
  refine ⟨F.img A, F.img B, F.isVine_img hA, F.isVine_img hB, ?_, F.img_union A B⟩
  rw [← F.img_inter, hi]
  unfold img
  simp [Finset.image_insert]

theorem isVC_img {S : Finset V} {a b : V} (h : IsVC M S a b) :
    IsVC N (F.img S) (F.e a) (F.e b) :=
  ⟨F.isBlock_img h.1, h.2.elim fun n hn => ⟨n, F.chain_img hn⟩⟩

theorem isHV_img {S : Finset V} {a b : V} (h : IsHV M S a b) :
    IsHV N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨x, hx, hv⟩ := h
  exact ⟨F.d x, F.ends_img hx, (F.erase x).isSomeVine_img hv⟩

theorem isHVC_img {S : Finset V} {a b : V} (h : IsHVC M S a b) :
    IsHVC N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨x, hx, hb, n, hn, hc⟩ := h
  exact ⟨F.d x, F.ends_img hx, (F.erase x).isBlock_img hb, n, hn, (F.erase x).chain_img hc⟩

theorem isStage1Group_img {S : Finset V} (h : IsStage1Group M S) : IsStage1Group N (F.img S) := by
  obtain ⟨a, b, h | h | h | h⟩ := h
  · exact ⟨F.e a, F.e b, Or.inl (F.isHV_img h)⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inl (F.isVC_img h))⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inr (Or.inl (F.isHVC_img h)))⟩
  · exact ⟨F.e a, F.e b, Or.inr (Or.inr (Or.inr (F.isDV_img h)))⟩

theorem img_img_symm (S : Finset V) : F.symm.img (F.img S) = S := by
  ext v
  rw [F.symm.mem_img']
  exact F.mem_img S v

theorem img_symm_img (S : Finset V') : F.img (F.symm.img S) = S := by
  ext v
  rw [F.mem_img']
  exact F.symm.mem_img S v

theorem maximalGroups_img {S : Finset V} (h : S ∈ maximalGroups M) : F.img S ∈ maximalGroups N := by
  refine ⟨F.isStage1Group_img h.1, fun T hT hST => ?_⟩
  have hT' : IsStage1Group M (F.symm.img T) := F.symm.isStage1Group_img hT
  have hsub : S ⊆ F.symm.img T := by
    have := (F.symm.img_subset_iff (S := F.img S) (T := T)).mpr hST
    rwa [F.img_img_symm] at this
  have := h.2 _ hT' hsub
  rw [← this, F.img_symm_img]

theorem maximalGroups_img_iff {S : Finset V} : F.img S ∈ maximalGroups N ↔ S ∈ maximalGroups M := by
  refine ⟨fun h => ?_, F.maximalGroups_img⟩
  simpa [F.img_img_symm] using F.symm.maximalGroups_img h

theorem vchain_img {S : Finset V} {a b : V} {n : ℕ} (h : Vine.Chain M S a b n) :
    Vine.Chain N (F.img S) (F.e a) (F.e b) n := by
  induction h with
  | single hv => exact Vine.Chain.single (F.isSomeVine_img hv)
  | append _ hT hi hne ih =>
    rw [F.img_union]
    refine Vine.Chain.append ih (F.isSomeVine_img hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

theorem chainIngredient_img {S A : Finset V} {a b x y : V} {n : ℕ}
    (h : Vine.ChainIngredient M S a b n A x y) :
    Vine.ChainIngredient N (F.img S) (F.e a) (F.e b) n (F.img A) (F.e x) (F.e y) := by
  induction h with
  | single hv => exact Vine.ChainIngredient.single (F.isSomeVine_img hv)
  | append_left _ hT hi hne ih =>
    rw [F.img_union]
    refine Vine.ChainIngredient.append_left ih (F.isSomeVine_img hT) ?_ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]
  | append_last hS hT hi hne =>
    rw [F.img_union]
    refine Vine.ChainIngredient.append_last (F.vchain_img hS) (F.isSomeVine_img hT) ?_
      (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

theorem isIngredient_img {S T : Finset V} (h : IsIngredient M S T) :
    IsIngredient N (F.img S) (F.img T) := by
  rcases h with ⟨a, b, n, x, y, hb, hc⟩ | ⟨a, b, x, n, p, q, hx, hn, hb, hc⟩
  · exact Or.inl ⟨F.e a, F.e b, n, F.e x, F.e y, F.isBlock_img hb, F.chainIngredient_img hc⟩
  · exact Or.inr ⟨F.e a, F.e b, F.d x, n, F.e p, F.e q, F.ends_img hx, hn,
      (F.erase x).isBlock_img hb, (F.erase x).chainIngredient_img hc⟩

theorem isIngredient_img_iff {S T : Finset V} : IsIngredient N (F.img S) (F.img T) ↔ IsIngredient M S T := by
  refine ⟨fun h => ?_, F.isIngredient_img⟩
  simpa [F.img_img_symm] using F.symm.isIngredient_img h

theorem deg_img (v : V) : N.deg (F.e v) = M.deg v := by
  unfold Molecule.deg
  apply card_bij (fun y _ => F.d.symm y)
  · intro y hy
    rw [Mole.mem_dartsAt] at hy ⊢
    have := F.symm.atom_comm y
    exact (this.trans (congrArg F.e.symm hy)).trans (F.e.symm_apply_apply v)
  · intro x _ y _ h
    exact F.d.symm.injective h
  · intro x hx
    refine ⟨F.d x, ?_, F.d.symm_apply_apply x⟩
    rw [Mole.mem_dartsAt] at hx ⊢
    exact (F.atom_comm x).trans (congrArg F.e hx)

theorem isSomeVine_img_iff {S : Finset V} {a b : V} :
    IsSomeVine N (F.img S) (F.e a) (F.e b) ↔ IsSomeVine M S a b := by
  refine ⟨fun h => ?_, F.isSomeVine_img⟩
  have := F.symm.isSomeVine_img h
  rw [F.img_img_symm] at this
  simpa [symm] using this

theorem isVC_img_iff {S : Finset V} {a b : V} : IsVC N (F.img S) (F.e a) (F.e b) ↔ IsVC M S a b := by
  refine ⟨fun h => ?_, F.isVC_img⟩
  have := F.symm.isVC_img h
  rw [F.img_img_symm] at this
  simpa [symm] using this

theorem isHVC_img_iff {S : Finset V} {a b : V} :
    IsHVC N (F.img S) (F.e a) (F.e b) ↔ IsHVC M S a b := by
  refine ⟨fun h => ?_, F.isHVC_img⟩
  have := F.symm.isHVC_img h
  rw [F.img_img_symm] at this
  simpa [symm] using this

end MolIso
end WaveTurbulence.Stage1
