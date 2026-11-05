/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Three-bond redexes in four-port graphs have disjoint vertex interiors

A branching node has a parent port and three ordered child ports. Source mini
pieces have three bonds between two branching nodes. The counting argument here
is independent of planar positions; its source-garden correspondence is separate.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Ports at u whose matched endpoint belongs to v. -/
def portsTo {α : Type*} [DecidableEq α] (mate : α × Fin 4 → α × Fin 4) (u v : α) : Finset (Fin 4) :=
  Finset.univ.filter fun i => (mate (u,i)).1 = v

/-- The three internal bonds of a source mini piece. -/
def ThreeBonds {α : Type*} [DecidableEq α] (mate : α × Fin 4 → α × Fin 4) (u v : α) : Prop :=
  3 ≤ (portsTo mate u v).card

/-- A vertex cannot have three bonds to each of two different neighbours. -/
theorem threeBonds_neighbour_unique {α : Type*} [DecidableEq α]
    (mate : α × Fin 4 → α × Fin 4) (u v z : α)
    (hv : ThreeBonds mate u v) (hz : ThreeBonds mate u z) : v = z := by
  by_contra hn
  have hd : Disjoint (portsTo mate u v) (portsTo mate u z) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hn (((Finset.mem_filter.mp hi).2).symm.trans (Finset.mem_filter.mp hj).2)
  have hc := Finset.card_union_of_disjoint hd
  have hu : ((portsTo mate u v) ∪ (portsTo mate u z)).card ≤ 4 := by
    have h := Finset.card_le_card (Finset.subset_univ ((portsTo mate u v) ∪ (portsTo mate u z)))
    simpa only [Finset.card_univ,Fintype.card_fin] using h
  change 3 ≤ (portsTo mate u v).card at hv
  change 3 ≤ (portsTo mate u z).card at hz
  omega

/-- Matching is an involution, so counting bonds does not depend on the endpoint. -/
theorem portsTo_card_symm {α : Type*} [DecidableEq α]
    (mate : α × Fin 4 → α × Fin 4) (hm : Function.Involutive mate) (u v : α) :
    (portsTo mate u v).card = (portsTo mate v u).card := by
  let f : Fin 4 → Fin 4 := fun i => (mate (u,i)).2
  have hi : Set.InjOn f (portsTo mate u v) := by
    intro i hi j hj hij
    have h : mate (u,i) = mate (u,j) := Prod.ext
      (((Finset.mem_filter.mp hi).2).trans (Finset.mem_filter.mp hj).2.symm) hij
    have he := hm.injective h
    exact congrArg Prod.snd he
  have he : (portsTo mate u v).image f = portsTo mate v u := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      have hv := (Finset.mem_filter.mp hi).2
      have hp : mate (u,i) = (v,f i) := Prod.ext hv rfl
      have hh := hm (u,i)
      rw [hp] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst hh⟩
    · intro hj
      have hu := (Finset.mem_filter.mp hj).2
      let i := (mate (v,j)).2
      have hp : mate (v,j) = (u,i) := Prod.ext hu rfl
      have hh := hm (v,j)
      rw [hp] at hh
      refine Finset.mem_image.mpr ⟨i,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst hh⟩
      · exact congrArg Prod.snd hh
  rw [← he,Finset.card_image_of_injOn hi]

theorem threeBonds_symm {α : Type*} [DecidableEq α]
    (mate : α × Fin 4 → α × Fin 4) (hm : Function.Involutive mate) (u v : α) :
    ThreeBonds mate u v ↔ ThreeBonds mate v u := by
  unfold ThreeBonds
  rw [portsTo_card_symm mate hm u v]

/-- Two distinct mini pieces cannot share a branching node. -/
theorem threeBonds_interiors_disjoint {α : Type*} [DecidableEq α]
    (mate : α × Fin 4 → α × Fin 4) (hm : Function.Involutive mate)
    (u v a b : α) (huv : ThreeBonds mate u v) (hab : ThreeBonds mate a b)
    (hne : ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))) :
    u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b := by
  have hvu := (threeBonds_symm mate hm u v).mp huv
  have hba := (threeBonds_symm mate hm a b).mp hab
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    subst a
    exact hne (Or.inl ⟨rfl,threeBonds_neighbour_unique mate u v b huv hab⟩)
  · intro h
    subst b
    exact hne (Or.inr ⟨rfl,threeBonds_neighbour_unique mate u v a huv hba⟩)
  · intro h
    subst a
    exact hne (Or.inr ⟨threeBonds_neighbour_unique mate v u b hvu hab,rfl⟩)
  · intro h
    subst b
    exact hne (Or.inl ⟨threeBonds_neighbour_unique mate v u a hvu hba,rfl⟩)

end WaveTurbulence.Reg.Skeleton
