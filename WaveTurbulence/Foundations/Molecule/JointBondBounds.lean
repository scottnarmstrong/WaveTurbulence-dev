/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTwistPlacements

/-! # A degree-two block joint cannot participate in a triple bond

TARGET twist: no embedded mini piece can involve the lower joint. This
follows from two internal and at most two external half-edge incidences.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset

/-- Three distinct actual bonds between two distinct atoms, with half-edge witnesses. -/
@[expose] def TripleBond {V D : Type*} (M : Molecule V D) (a b : V) : Prop :=
  ∃ f : Fin 3 → D, Function.Injective f ∧ (∀ i, M.atom (f i) = a) ∧
    ∀ i, M.atom (M.mate (f i)) = b

/-- Three actual incidences force bond multiplicity at least three. -/
theorem TripleBond.count {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} {a b : V} (h : TripleBond M a b) (hne : a ≠ b) : 3 ≤ M.bondsBetween a b := by
  obtain ⟨f,hf,ha,hb⟩ := h
  rw [Mole.bondsBetween_eq_card_darts M hne]
  have hs : univ.image f ⊆ (M.dartsAt a).filter (fun x => M.atom (M.mate x) = b) := by
    intro x hx
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a _).mpr (ha i),hb i⟩
  have hc := card_le_card hs
  simpa only [card_image_of_injective _ hf,card_univ,Fintype.card_fin] using hc

/-- Reversing all three darts gives the reverse triple bond. -/
theorem TripleBond.symm {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {a b : V} (h : TripleBond M a b) : TripleBond M b a := by
  obtain ⟨f,hf,ha,hb⟩ := h
  refine ⟨M.mate ∘ f,(Mole.mate_injective M).comp hf,hb,?_⟩
  intro i
  change M.atom (M.mate (M.mate (f i))) = a
  rw [M.mate_mate]
  exact ha i

/-- Every distinct-neighbor bond multiplicity at a degree-two block joint is at most two. -/
theorem block_joint_bonds_le_two {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b q : V}
    (hB : M.IsBlock S a b) (hq : b ≠ q) : M.bondsBetween b q ≤ 2 := by
  rw [Mole.bondsBetween_eq_card_darts M hq]
  let I := (M.dartsAt b).filter (M.InGroup S)
  have hI : I.card = 2 := (Mole.block_joint_degrees M hB).2
  by_cases hqS : q ∈ S
  · apply (card_le_card ?_).trans (le_of_eq hI)
    intro x hx
    obtain ⟨hx,hq⟩ := mem_filter.mp hx
    have hb := (Mole.mem_dartsAt M b x).mp hx
    exact mem_filter.mpr ⟨hx,by
      change M.atom x ∈ S ∧ M.atom (M.mate x) ∈ S
      rw [hb,hq]; exact ⟨hB.2.2.1,hqS⟩⟩
  · have hs : (M.dartsAt b).filter (fun x => M.atom (M.mate x) = q) ⊆ M.dartsAt b \ I := by
      intro x hx
      obtain ⟨hx,hq⟩ := mem_filter.mp hx
      refine mem_sdiff.mpr ⟨hx,?_⟩
      intro hi
      have hm := (mem_filter.mp hi).2.2
      exact hqS (hq ▸ hm)
    have hc := card_le_card hs
    have hd := Mole.deg_le_four M hM (hB.1 hB.2.2.1)
    have he : (M.dartsAt b \ I).card = (M.dartsAt b).card - I.card :=
      card_sdiff_of_subset (filter_subset _ _)
    rw [he,hI] at hc
    change (M.dartsAt b).card ≤ 4 at hd
    omega

/-- No triple bond at the lower joint of any actual current source block. -/
theorem block_joint_no_triple {w : ℕ} (G : Garden w) {S : Finset (GBranch G.tree)}
    {a b q : GBranch G.tree} (hB : G.molecule.IsBlock S a b) (hq : b ≠ q) :
    ¬ TripleBond G.molecule b q := by
  intro ht
  have hcount := ht.count hq
  have hbound := block_joint_bonds_le_two G.molecule (Mole.garden_isMolecule G) hB hq
  omega

end WaveTurbulence.Twist
