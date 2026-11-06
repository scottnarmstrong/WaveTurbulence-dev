/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamFinal
public import WaveTurbulenceVineParam.VineParamBasePhysicalExistence
public import WaveTurbulenceVineParam.VineParamGroupInsert
public import WaveTurbulenceVineParam.VineParamGroupExpand
public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # VINEPARAM-GROUPS: a full vine chart whose groups are the cohmol groups (R22(3))

`vineparam_grouped`: for every vine and every realization `R` of it (the witnesses of the pinned
`IsVine`), there is a `FullVineChart` whose groups, namely the rung pairs
`{atom (xSlot j), atom (ySlot j)}` and (for the normal types) the core triple
`{atom (uSlot 0), atom (uSlot 1), atom (uSlot 2)}`, are exactly the atom sets of
`Vine.realizedGroups R` (TARGET Def `cohmol`, L1489).
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The groups of a full chart: its rung pairs and its core triple, as sets of actual atoms. -/
@[expose] def chartAtomGroups {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (F : FullVineChart M X S a b) : Finset (Finset V) :=
  shapeGroupSet F.indexing.shape (fun i => (F.indexing.atom i).1)

/-- The cohmol groups of a realization, as sets of actual atoms. -/
@[expose] noncomputable def realizedGroupSet {M : Molecule V D} {X : VineType} {S : Finset V}
    {a b : V} (R : VineRealization M X S a b) : Finset (Finset V) :=
  ((realizedGroups R).map List.toFinset).toFinset

theorem chartAtomGroups_subset {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (F : FullVineChart M X S a b) : ∀ s ∈ chartAtomGroups F, s ⊆ S := by
  have hat : ∀ i, (F.indexing.atom i).1 ∈ S := fun i =>
    (mem_erase.mp (F.indexing.atom i).2).2
  intro s hs
  unfold chartAtomGroups shapeGroupSet at hs
  rcases mem_union.mp hs with hs | hs
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hs
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> exact hat _
  · split_ifs at hs with hn
    · rw [mem_singleton] at hs
      subst hs
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> exact hat _
    · exact absurd hs (notMem_empty _)

theorem realizedGroupSet_subset {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) : ∀ s ∈ realizedGroupSet R, s ⊆ S := by
  intro s hs
  unfold realizedGroupSet realizedGroups at hs
  simp only [List.mem_toFinset, List.mem_map] at hs
  obtain ⟨l, ⟨g, _, rfl⟩, rfl⟩ := hs
  intro v hv
  have := List.mem_toFinset.mp hv
  exact Finset.mem_toList.mp (List.mem_filter.mp this).1

omit [DecidableEq V] in
/-- Images of finite families of subsets of `S` under a map injective on `S` determine the family. -/
theorem groups_eq_of_image {S : Finset V} {f : V → ℕ} (hinj : Set.InjOn f S)
    (A B : Finset (Finset V)) (hA : ∀ s ∈ A, s ⊆ S) (hB : ∀ s ∈ B, s ⊆ S)
    (h : A.image (Finset.image f) = B.image (Finset.image f)) : A = B := by
  have key : ∀ s t : Finset V, s ⊆ S → t ⊆ S → s.image f = t.image f → s = t := by
    intro s t hs ht hst
    ext v
    constructor
    · intro hv
      have : f v ∈ t.image f := hst ▸ mem_image_of_mem f hv
      obtain ⟨w, hw, hwv⟩ := mem_image.mp this
      have := hinj (ht hw) (hs hv) hwv
      exact this ▸ hw
    · intro hv
      have : f v ∈ s.image f := hst.symm ▸ mem_image_of_mem f hv
      obtain ⟨w, hw, hwv⟩ := mem_image.mp this
      have := hinj (hs hw) (ht hv) hwv
      exact this ▸ hw
  ext s
  constructor
  · intro hs
    have : s.image f ∈ B.image (Finset.image f) := h ▸ mem_image_of_mem _ hs
    obtain ⟨t, ht, hts⟩ := mem_image.mp this
    exact (key t s (hB t ht) (hA s hs) hts) ▸ ht
  · intro hs
    have : s.image f ∈ A.image (Finset.image f) := h.symm ▸ mem_image_of_mem _ hs
    obtain ⟨t, ht, hts⟩ := mem_image.mp this
    exact (key t s (hA t ht) (hB s hs) hts) ▸ ht

theorem mem_realizedGroupSet {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (s : Finset V) :
    s ∈ realizedGroupSet R ↔
      ∃ g ∈ (X.expand R.k).groups, s = S.filter (fun v => R.f v ∈ g) := by
  unfold realizedGroupSet realizedGroups
  rw [List.mem_toFinset, List.map_map]
  constructor
  · intro h
    obtain ⟨g, hg, hgs⟩ := List.mem_map.mp h
    refine ⟨g, hg, ?_⟩
    rw [← hgs]
    ext v
    simp
  · rintro ⟨g, hg, rfl⟩
    refine List.mem_map.mpr ⟨g, hg, ?_⟩
    ext v
    simp

/-- The cohmol groups of a realization, read through the labelling `R.f`. -/
theorem realizedGroupSet_image {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) :
    (realizedGroupSet R).image (Finset.image R.f) = listGroupSet (X.expand R.k).groups := by
  have himg : ∀ g ∈ (X.expand R.k).groups,
      (S.filter (fun v => R.f v ∈ g)).image R.f = g.toFinset := by
    intro g hg
    ext x
    simp only [mem_image, mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro hx
      have hlt : x < (X.expand R.k).n :=
        ((mem_expand_groups_iff X R.k x).mp (List.mem_flatten.mpr ⟨g, hg, hx⟩)).2
      have hx' : x ∈ S.image R.f := R.image_eq.symm ▸ mem_range.mpr hlt
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx'
      exact ⟨v, ⟨hv, hx⟩, rfl⟩
  ext t
  rw [mem_listGroupSet]
  simp only [mem_image, mem_realizedGroupSet]
  constructor
  · rintro ⟨s, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, (himg g hg).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, himg g hg⟩


/-- A chart with the cohmol groups bounds the incoherency index of the vine by the number of
chart groups that are not in a single layer (V5's `n_(3)` bound). -/
theorem realizedIncoherencyIndex_le_chartGroups {L : Type*} [DecidableEq L] {M : Molecule V D}
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (F : FullVineChart M X S a b) (hF : chartAtomGroups F = realizedGroupSet R) (layer : V → L) :
    realizedIncoherencyIndex R layer ≤
      ((chartAtomGroups F).filter (fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y)).card := by
  classical
  unfold realizedIncoherencyIndex incoherencyIndex
  set Ls := realizedGroups R with hLs
  set L' := Ls.filter (fun g => ¬ GroupCoherent layer g) with hL'
  have hdisj : Ls.Pairwise List.Disjoint := (List.nodup_flatten.mp (actual_groups_nodup R)).2
  have hsub : L'.Pairwise List.Disjoint := hdisj.sublist (List.filter_sublist)
  have hne : ∀ g ∈ L', g ≠ [] := by
    intro g hg hg0
    have := (List.mem_filter.mp hg).2
    subst hg0
    simp [GroupCoherent] at this
  have hnd : (L'.map List.toFinset).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine (List.Pairwise.and_mem.mp hsub).imp ?_
    rintro x y ⟨hx, hy, hxy⟩ hEq
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil x (hne x hx)
    have : e ∈ y.toFinset := hEq ▸ List.mem_toFinset.mpr he
    exact hxy he (List.mem_toFinset.mp this)
  have hcard : L'.length = (L'.map List.toFinset).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard]
  apply Finset.card_le_card
  intro s hs
  rw [List.mem_toFinset, List.mem_map] at hs
  obtain ⟨g, hg, rfl⟩ := hs
  have hg' := List.mem_filter.mp hg
  rw [Finset.mem_filter, hF]
  refine ⟨?_, ?_⟩
  · unfold realizedGroupSet
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨g, hg'.1, rfl⟩)
  · intro hco
    apply (of_decide_eq_true hg'.2)
    intro x hx y hy
    exact hco x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)

/-- `VINEPARAM-GROUPS`, conditional on the base-template statement (with groups). -/
theorem vineparam_grouped_of_base (hBase : ∀ X : VineType,BaseChartStatement X) :
    ∀ (V D : Type) [DecidableEq V] [Fintype D] (M : Molecule V D), M.IsMolecule →
      ∀ (X : VineType) (S : Finset V) (a b : V), M.IsVine X S a b →
        ∀ R : VineRealization M X S a b,
          ∃ F : FullVineChart M X S a b, chartAtomGroups F = realizedGroupSet R := by
  intro V D _ _ M hM X S a b hV R
  classical
  have hBl0 := (isVine_iff_realization.mp hV).1
  have hBl := degreeBlock_of_isBlock M hBl0
  obtain ⟨e,hshape,_⟩ := exists_realized_directed_model hM R hBl
  let Q := realizationBondModel R e
  have hdeg := realization_directed_degrees M hM R hBl
  have hshadow : (univ : Finset (Fin (X.expand R.k).bonds.length)).val.map
      (fun j => s((Q.ends j).1.1,(Q.ends j).2.1)) = bondSym (X.expand R.k).bonds := by
    have h1 : (univ : Finset (Fin (X.expand R.k).bonds.length)).val.map
        (fun j => s((Q.ends j).1.1,(Q.ends j).2.1)) =
        ((List.ofFn (realizedEnds R e) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map (fun p => s(p.1,p.2)) := by
      rw [Multiset.map_coe,List.map_ofFn,← Fin.univ_val_map]
      rfl
    rw [h1,hshape]
    rfl
  have hbal : ∀ v,(∑ j,-energySign Q.ends v j) = 0 := by
    intro v
    have hq := hdeg v
    have ht := tail_count M S e (R.atomAt v).1
    have hh := head_count M S e (R.atomAt v).1
    have hc1 : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter fun j => (Q.ends j).1 = v).card =
        ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
          fun i => M.atom (e i).1 = (R.atomAt v).1).card := by
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [← Q.atom_val_eq_iff,← Q.tail j]
      rfl
    have hc2 : ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter fun j => (Q.ends j).2 = v).card =
        ((univ : Finset (Fin (X.expand R.k).bonds.length)).filter
          fun i => M.atom (M.mate (e i).1) = (R.atomAt v).1).card := by
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [← Q.atom_val_eq_iff,← Q.head j]
      rfl
    simp only [energySign,neg_sub]
    rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole,hc1,hc2,ht,hh,hq.1,hq.2]
    simp
  have hab := hBl.2.2.2.1
  have hj := R.joints_eq
  have hfa : R.f a ∈ ({0,1} : Finset ℕ) := hj ▸ Finset.mem_insert_self _ _
  have hfb : R.f b ∈ ({0,1} : Finset ℕ) := hj ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hne : R.f a ≠ R.f b := fun h => hab (R.injOn hBl.2.1 hBl.2.2.1 h)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hfa hfb
  let D' : ExpData X R.k Q.ends := { lab := Equiv.refl _,shadow := hshadow,balanced := hbal }
  let a' : Fin (X.expand R.k).n := (realizationAtomEquiv R).symm ⟨a,hBl.2.1⟩
  let b' : Fin (X.expand R.k).n := (realizationAtomEquiv R).symm ⟨b,hBl.2.2.1⟩
  have hjb : R.f b < 2 := by omega
  obtain ⟨P,-,-,hgr⟩ := exists_physical_expanded X (hBase X) _ R.k rfl R.length_eq
    (Fin (X.expand R.k).n) (Fin (X.expand R.k).bonds.length) Q.ends D' a' b' ⟨R.f b,hjb⟩
    (by change R.f a = 1-R.f b; omega) rfl
  have e1 : (Q.atom a').1 = a := by
    change ((realizationAtomEquiv R) ((realizationAtomEquiv R).symm ⟨a,hBl.2.1⟩)).1 = a
    rw [Equiv.apply_symm_apply]
  have e2 : (Q.atom b').1 = b := by
    change ((realizationAtomEquiv R) ((realizationAtomEquiv R).symm ⟨b,hBl.2.2.1⟩)).1 = b
    rw [Equiv.apply_symm_apply]
  have hex : ∃ F : FullVineChart M X S (Q.atom a').1 (Q.atom b').1,
      chartAtomGroups F = realizedGroupSet R := by
    refine ⟨Q.pullFullChart P.full P.distinct, ?_⟩
    apply groups_eq_of_image (f := R.f) R.injOn
    · exact chartAtomGroups_subset _
    · exact realizedGroupSet_subset R
    · rw [realizedGroupSet_image R]
      unfold chartAtomGroups
      have hfun : (fun i => R.f ((Q.pullFullChart P.full P.distinct).indexing.atom i).1) =
          fun i => (D'.lab (P.full.indexing.atom i).1).1 := by
        funext i
        change R.f ((realizationAtomEquiv R (P.full.indexing.atom i).1).1) = _
        exact R.label_atomAt _
      have hmap := shapeGroupSet_map (Q.pullFullChart P.full P.distinct).indexing.shape
        (fun i => ((Q.pullFullChart P.full P.distinct).indexing.atom i).1) R.f
      rw [← hmap, hfun]
      exact hgr
  rw [e1,e2] at hex
  exact hex

/-- **VINEPARAM-GROUPS** (R22(3)): every vine, with any realization `R` of it, has a full chart
whose rung pairs and core triple are exactly the cohmol groups of `R`. -/
theorem vineparam_grouped :
    ∀ (V D : Type) [DecidableEq V] [Fintype D] (M : Molecule V D), M.IsMolecule →
      ∀ (X : VineType) (S : Finset V) (a b : V), M.IsVine X S a b →
        ∀ R : VineRealization M X S a b,
          ∃ F : FullVineChart M X S a b, chartAtomGroups F = realizedGroupSet R :=
  vineparam_grouped_of_base (fun X {_m} A hU hdeg joint a b ha hb =>
    exists_physical_base_chart X A hU hdeg joint a b ha hb)

end WaveTurbulence.Vine.Param
