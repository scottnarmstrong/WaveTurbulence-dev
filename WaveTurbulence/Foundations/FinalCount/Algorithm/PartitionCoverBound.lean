/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Pairwise
import Mathlib.Tactic

/-! # A finite partition's complexity is bounded by cover pieces and uncovered atoms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V : Type*} [DecidableEq V]

theorem partition_cover_complexity_bound (A : Finset V) (F C : Finset (Finset V))
    (hF : (F : Set (Finset V)).PairwiseDisjoint id) (hFA : ∀ T ∈ F,T ⊆ A) (hFn : ∀ T ∈ F,T.Nonempty)
    (hCn : ∀ S ∈ C,S.Nonempty) (hparent : ∀ S ∈ C,∃ T ∈ F,S ⊆ T) :
    F.card+(A \ F.biUnion id).card ≤ C.card+(A \ C.biUnion id).card := by
  classical
  let Hit : Finset (Finset V) := F.filter fun T => ∃ S ∈ C,S ⊆ T
  let Miss : Finset (Finset V) := F.filter fun T => ¬∃ S ∈ C,S ⊆ T
  let Free := A \ F.biUnion id
  let Left := A \ C.biUnion id
  have unique_parent {T U S : Finset V} (hT : T ∈ F) (hU : U ∈ F) (hn : S.Nonempty)
      (hST : S ⊆ T) (hSU : S ⊆ U) : T = U := by
    by_contra hne
    obtain ⟨a,ha⟩ := hn
    exact disjoint_left.mp (hF hT hU hne) (hST ha) (hSU ha)
  have hhit : Hit.card ≤ C.card := by
    have hc : ∀ T : Hit,∃ S : C,S.val ⊆ T.val := by
      intro T
      obtain ⟨S,hS,hST⟩ := (mem_filter.mp T.property).2
      exact ⟨⟨S,hS⟩,hST⟩
    let f : Hit → C := fun T => (hc T).choose
    have hf : Function.Injective f := by
      intro T U he
      apply Subtype.ext
      apply unique_parent (mem_filter.mp T.property).1 (mem_filter.mp U.property).1
        (hCn (f T).val (f T).property) (hc T).choose_spec
      have hST := (hc U).choose_spec
      change (f U).val ⊆ U.val at hST
      rw [he]
      exact hST
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_finsetCard] using hh
  have hfree : Free ⊆ Left := by
    intro a ha
    obtain ⟨haA,haF⟩ := mem_sdiff.mp ha
    apply mem_sdiff.mpr
    refine ⟨haA,?_⟩
    intro h
    obtain ⟨S,hS,haS⟩ := mem_biUnion.mp h
    obtain ⟨T,hT,hST⟩ := hparent S hS
    exact haF (mem_biUnion.mpr ⟨T,hT,hST haS⟩)
  have hmiss : Miss.card ≤ (Left \ Free).card := by
    have hc : ∀ T : Miss,∃ a ∈ T.val,a ∈ Left \ Free := by
      intro T
      obtain ⟨a,ha⟩ := hFn T.val (mem_filter.mp T.property).1
      refine ⟨a,ha,mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hFA _ (mem_filter.mp T.property).1 ha,?_⟩,?_⟩⟩
      · intro h
        obtain ⟨S,hS,haS⟩ := mem_biUnion.mp h
        obtain ⟨U,hU,hSU⟩ := hparent S hS
        have he : U = T.val := by
          by_contra hn
          exact disjoint_left.mp (hF hU (mem_filter.mp T.property).1 hn) (hSU haS) ha
        exact (mem_filter.mp T.property).2 ⟨S,hS,he ▸ hSU⟩
      · intro h
        exact (mem_sdiff.mp h).2 (mem_biUnion.mpr ⟨T.val,(mem_filter.mp T.property).1,ha⟩)
    let f : ↥Miss → ↥(Left \ Free) := fun T => ⟨(hc T).choose,(hc T).choose_spec.2⟩
    have hf : Function.Injective f := by
      intro T U he
      apply Subtype.ext
      by_contra hn
      have hval : (hc T).choose = (hc U).choose := congrArg Subtype.val he
      have haT := (hc T).choose_spec.1
      have haU := (hc U).choose_spec.1
      rw [← hval] at haU
      exact disjoint_left.mp (hF (mem_filter.mp T.property).1 (mem_filter.mp U.property).1 hn) haT haU
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_finsetCard] using hh
  have hparts : Hit.card+Miss.card = F.card := card_filter_add_card_filter_not _
  have hleft : (Left \ Free).card+Free.card = Left.card := card_sdiff_add_card_eq_card hfree
  change F.card+Free.card ≤ C.card+Left.card
  omega

end WaveTurbulence.Mole.AppbAlgorithm
