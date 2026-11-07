/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.ChainResidual
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitRank
import Mathlib.Tactic

/-! # The β-cut exclusion of DH23 Prop 10.4(1)

DH23 L1838: "one cannot make a β-cut in `𝕄` such that one of the new components has all atoms of degree 4 except the
newly formed β-atom which has degree 2". With B2's `cut` (`x₁, x₂` stay at `v`, all other darts move to the fresh
atom `v₂`), the newly formed degree-two β-atom is `v`. A (Y) sequence ending in (Y1) case 3 produces exactly such a
cut, at the common far end `w` of the two exits (DH23 L1959: "cannot be (Y1) case 3 due to the β-cut assumption").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **DH23's excluded β-cut** (Prop 10.4(1)): a β-cut whose new component through the degree-two atom `v` has every
other atom of degree four. -/
def HasBadBetaCut (M : Molecule V D) : Prop :=
  ∃ v v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ ∧ ¬ M.IsAlphaCut v v₂ x₁ x₂ ∧
    ∀ u ∈ (M.cut v v₂ x₁ x₂).atoms, (M.cut v v₂ x₁ x₂).SameComponent v u → u ≠ v → (M.cut v v₂ x₁ x₂).deg u = 4

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- A set closed under adjacency is a union of components. -/
theorem mem_iff_of_sameComponent_of_closed {K : Molecule V D} {S : Finset V}
    (hS : ∀ z, K.atom z ∈ S → K.atom (K.mate z) ∈ S) {a b : V} (h : K.SameComponent a b) : a ∈ S ↔ b ∈ S := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    refine ⟨hS z, fun hb => ?_⟩
    have := hS (K.mate z) hb
    rwa [K.mate_mate] at this
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

namespace Pinch
variable {M : Molecule V D} (T : Pinch M)

section
variable {v₂ : V} (hv₂ : v₂ ∉ M.atoms)
include hv₂

theorem cutData : M.IsCutData T.w v₂ (M.mate T.x) (M.mate T.y) := by
  refine ⟨M.atom_mem _, hv₂, rfl, T.same.symm, ?_, ?_, ?_⟩
  · rw [M.mate_mate]
    intro h
    have h1 := T.atom_x
    rw [← h] at h1
    exact T.w_notMem (by unfold Pinch.w; rw [T.same]; exact h1)
  · rw [M.out_mate, T.out_x]; rfl
  · rw [M.out_mate, T.out_y]; rfl

omit hv₂ in
/-- The cut atom keeps exactly the two exits. -/
theorem cut_atom_eq (z : D) :
    (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).atom z =
      if M.atom z = T.w ∧ z ≠ M.mate T.x ∧ z ≠ M.mate T.y then v₂ else M.atom z := rfl

omit hv₂ in
theorem cut_atom_of_ne {z : D} (h : M.atom z ≠ T.w) :
    (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).atom z = M.atom z := by
  rw [T.cut_atom_eq]; simp [h]

/-- **The component of `w` after the cut is `Y ∪ {w}`.** -/
theorem cut_component_sub {u : V} (h : (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).SameComponent T.w u) :
    u ∈ insert T.w T.Y := by
  set K := M.cut T.w v₂ (M.mate T.x) (M.mate T.y)
  have hv₂w : v₂ ≠ T.w := fun h => hv₂ (h ▸ M.atom_mem _)
  have hclosed : ∀ z, K.atom z ∈ insert T.w T.Y → K.atom (K.mate z) ∈ insert T.w T.Y := by
    intro z hz
    change K.atom (M.mate z) ∈ _
    rcases mem_insert.mp hz with hw | hY
    · -- `z` is one of the two kept darts at `w`
      rw [T.cut_atom_eq] at hw
      split_ifs at hw with hmv
      · exact absurd hw hv₂w
      · have hzw : M.atom z = T.w := hw
        have hz2 : z = M.mate T.x ∨ z = M.mate T.y := by
          by_contra hno; push Not at hno; exact hmv ⟨hzw, hno⟩
        rcases hz2 with rfl | rfl
        · rw [M.mate_mate, T.cut_atom_of_ne (v₂ := v₂) (fun h => T.w_notMem (h ▸ T.atom_x))]
          exact mem_insert_of_mem T.atom_x
        · rw [M.mate_mate, T.cut_atom_of_ne (v₂ := v₂) (fun h => T.w_notMem (h ▸ T.atom_y))]
          exact mem_insert_of_mem T.atom_y
    · have hzM : M.atom z ∈ T.Y := by
        rw [T.cut_atom_eq] at hY
        split_ifs at hY
        · exact absurd (T.sub hY) hv₂
        · exact hY
      by_cases hm : M.atom (M.mate z) ∈ T.Y
      · rw [T.cut_atom_of_ne (v₂ := v₂) (fun h => T.w_notMem (h ▸ hm))]; exact mem_insert_of_mem hm
      · have hc : z ∈ crossDarts M T.Y := mem_crossDarts.mpr ⟨hzM, hm⟩
        rw [T.cross] at hc
        rcases mem_insert.mp hc with rfl | h
        · rw [T.cut_atom_eq]; simp [Pinch.w]
        · rw [mem_singleton.mp h, T.cut_atom_eq]; simp [Pinch.w, T.same]
  exact (mem_iff_of_sameComponent_of_closed hclosed h).mp (mem_insert_self _ _)

omit hv₂ in
/-- Away from `w` and the new atom, degrees are unchanged by the cut. -/
theorem cut_deg_of_ne {u : V} (hu : u ≠ T.w) (hu2 : u ≠ v₂) :
    (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).deg u = M.deg u := by
  classical
  unfold Molecule.deg Molecule.dartsAt
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and]
  rw [T.cut_atom_eq]
  split_ifs with h
  · exact ⟨fun h' => absurd h'.symm hu2, fun h' => absurd (h'.symm.trans h.1) hu⟩
  · exact Iff.rfl

/-- Adjacency after the cut is adjacency before it, with the new atom read as `w`. -/
theorem cut_sameComponent_fold {a b : V} (h : (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).SameComponent a b) :
    M.SameComponent (if a = v₂ then T.w else a) (if b = v₂ then T.w else b) := by
  have hv₂w : v₂ ≠ T.w := fun h => hv₂ (h ▸ M.atom_mem _)
  have hfold : ∀ z, (if (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).atom z = v₂ then T.w else
      (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).atom z) = M.atom z := by
    intro z
    rw [T.cut_atom_eq]
    split_ifs with h1 h2
    · exact h1.1.symm
    · exact absurd rfl h2
    · rename_i h3; exact absurd (h3 ▸ M.atom_mem z) hv₂
    · rfl
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    rw [hfold z]
    have := hfold (M.mate z)
    change (if (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).atom (M.mate z) = v₂ then T.w else _) = _ at this
    rw [show (M.cut T.w v₂ (M.mate T.x) (M.mate T.y)).mate z = M.mate z from rfl, this]
    exact Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **The cut at `w` is a β-cut**: it splits off `Y ∪ {w}` from the new atom. -/
theorem cut_not_alpha : ¬ M.IsAlphaCut T.w v₂ (M.mate T.x) (M.mate T.y) := by
  classical
  set K := M.cut T.w v₂ (M.mate T.x) (M.mate T.y)
  have hv₂w : v₂ ≠ T.w := fun h => hv₂ (h ▸ M.atom_mem _)
  have hKatoms : K.atoms = insert v₂ M.atoms := rfl
  have hwK : T.w ∈ K.atoms := mem_insert_of_mem (M.atom_mem _)
  have hv₂K : v₂ ∈ K.atoms := mem_insert_self _ _
  let ψ : V → V := fun u => if u = v₂ then T.w else u
  set B := Degen.componentSet K v₂
  have hBne : ∀ u ∈ K.atoms, u ∉ B → Degen.componentSet K u ≠ B := by
    intro u hu huB h
    apply huB
    rw [← h, Degen.mem_componentSet]; exact ⟨hu, Relation.EqvGen.refl _⟩
  unfold Molecule.IsAlphaCut
  rw [Degen.numComponents_eq_card_componentSets, Degen.numComponents_eq_card_componentSets]
  push Not
  change (Degen.componentSets M).card < (Degen.componentSets K).card
  -- the components of `M` are the images of those of `K` other than `B`
  have hM : Degen.componentSets M = (K.atoms \ B).image fun u => Degen.componentSet M (ψ u) := by
    unfold Degen.componentSets
    ext S
    simp only [mem_image, mem_sdiff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu2 : u ≠ v₂ := fun h => hv₂ (h ▸ hu)
      by_cases huB : u ∈ B
      · refine ⟨T.w, ⟨hwK, ?_⟩, ?_⟩
        · intro hwB
          rw [Degen.mem_componentSet] at hwB
          have := T.cut_component_sub hv₂ (Relation.EqvGen.symm _ _ hwB.2)
          rcases mem_insert.mp this with h | h
          · exact hv₂w h
          · exact hv₂ (T.sub h)
        · simp only [ψ, hv₂w.symm, ite_false]
          rw [Degen.mem_componentSet] at huB
          have := T.cut_sameComponent_fold hv₂ huB.2
          simp only [ite_true, hu2, ite_false] at this
          exact (Degen.componentSet_eq_iff M (M.atom_mem _)).mpr this
      · exact ⟨u, ⟨mem_insert_of_mem hu, huB⟩, by simp only [ψ, hu2, ite_false]⟩
    · rintro ⟨u, ⟨hu, _⟩, rfl⟩
      by_cases hu2 : u = v₂
      · exact ⟨T.w, M.atom_mem _, by simp only [ψ, hu2, ite_true]⟩
      · refine ⟨u, ?_, by simp only [ψ, hu2, ite_false]⟩
        rw [hKatoms] at hu
        exact (mem_insert.mp hu).resolve_left hu2
  have hK : (K.atoms \ B).image (Degen.componentSet K) = (Degen.componentSets K).erase B := by
    unfold Degen.componentSets
    ext S
    simp only [mem_image, mem_sdiff, mem_erase]
    constructor
    · rintro ⟨u, ⟨hu, huB⟩, rfl⟩
      exact ⟨hBne u hu huB, u, hu, rfl⟩
    · rintro ⟨hSB, u, hu, rfl⟩
      refine ⟨u, ⟨hu, fun huB => hSB ?_⟩, rfl⟩
      rw [Degen.mem_componentSet] at huB
      exact ((Degen.componentSet_eq_iff K hv₂K).mpr huB.2).symm
  have hle : ((K.atoms \ B).image fun u => Degen.componentSet M (ψ u)).card ≤
      ((K.atoms \ B).image (Degen.componentSet K)).card := by
    refine card_image_le_of_factor _ _ _ fun u hu v hv he => ?_
    have hs := (Degen.componentSet_eq_iff K (mem_sdiff.mp hu).1).mp he
    have hf := T.cut_sameComponent_fold hv₂ hs
    exact (Degen.componentSet_eq_iff M (by
      by_cases h : u = v₂
      · simp only [ψ, h, ite_true]; exact M.atom_mem _
      · simp only [ψ, h, ite_false]; exact (mem_insert.mp (mem_sdiff.mp hu).1).resolve_left h)).mpr hf
  have hBmem : B ∈ Degen.componentSets K := by unfold Degen.componentSets; exact mem_image_of_mem _ hv₂K
  rw [hM]
  rw [hK, card_erase_of_mem hBmem] at hle
  have hpos := card_pos.mpr ⟨B, hBmem⟩
  omega

/-- **A (Y1) case 3 ending gives DH23's excluded β-cut.** -/
theorem hasBadBetaCut (hdegY : ∀ u ∈ T.Y, M.deg u = 4) : HasBadBetaCut M := by
  refine ⟨T.w, v₂, M.mate T.x, M.mate T.y, T.cutData hv₂, T.cut_not_alpha hv₂, fun u _ hu hne => ?_⟩
  have hY := T.cut_component_sub hv₂ hu
  rcases mem_insert.mp hY with h | h
  · exact absurd h hne
  · rw [T.cut_deg_of_ne (v₂ := v₂) hne (fun h' => hv₂ (h' ▸ T.sub h))]
    exact hdegY u h

end
end Pinch
end WaveTurbulence.MoleProp4
