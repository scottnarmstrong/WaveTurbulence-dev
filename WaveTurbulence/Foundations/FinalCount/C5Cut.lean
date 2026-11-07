/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5Basic
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BetaCut
import Mathlib.Tactic

/-! # Prop 9.6, case (5): cuts, components, and lifting a `β`-cut through a chain removal -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A `β`-cut of a connected molecule separates the new atom from the cut atom. -/
theorem not_sameComponent_of_not_alpha (N : Molecule V D)
    (hconn : ∀ u ∈ N.atoms, ∀ w ∈ N.atoms, N.SameComponent u w) {v v₂ : V} {x₁ x₂ : D}
    (hc : N.IsCutData v v₂ x₁ x₂) (hna : ¬ N.IsAlphaCut v v₂ x₁ x₂) :
    ¬ (N.cut v v₂ x₁ x₂).SameComponent v v₂ := by
  classical
  intro hvv
  apply hna
  set K := N.cut v v₂ x₁ x₂ with hK
  have hKat : K.atoms = insert v₂ N.atoms := rfl
  have hdart : ∀ z, K.SameComponent (N.atom z) (K.atom z) := by
    intro z
    by_cases h : N.atom z = v ∧ z ≠ x₁ ∧ z ≠ x₂
    · have : K.atom z = v₂ := by change (if _ then _ else _) = _; rw [if_pos h]
      rw [this, h.1]; exact hvv
    · have : K.atom z = N.atom z := by change (if _ then _ else _) = _; rw [if_neg h]
      rw [this]; exact Relation.EqvGen.refl _
  have hfold : ∀ a b, N.SameComponent a b → K.SameComponent a b := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨z, rfl, rfl⟩ := hab
      have h1 := hdart z
      have h2 := hdart (N.mate z)
      have h3 : K.SameComponent (K.atom z) (K.atom (N.mate z)) := Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩
      exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h3 (Relation.EqvGen.symm _ _ h2))
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hKconn : ∀ a ∈ K.atoms, ∀ b ∈ K.atoms, K.SameComponent a b := by
    have hall : ∀ a ∈ K.atoms, K.SameComponent v a := by
      intro a ha
      rw [hKat] at ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hvv
      · exact hfold _ _ (hconn v hc.1 a ha)
    intro a ha b hb
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall a ha)) (hall b hb)
  have h1 : K.numComponents = 1 := Mole.numComponents_eq_one K ⟨v, by rw [hKat]; exact mem_insert_of_mem hc.1⟩ hKconn
  have h2 : N.numComponents = 1 := Mole.numComponents_eq_one N ⟨v, hc.1⟩ hconn
  unfold Molecule.IsAlphaCut
  rw [← hK, h1, h2]

/-- If the cut atom and the new atom lie in different components, the cut is a `β`-cut. -/
theorem not_alpha_of_not_sameComponent (M : Molecule V D)
    (hconn : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, M.SameComponent u w) {v v₂ : V} {x₁ x₂ : D}
    (hc : M.IsCutData v v₂ x₁ x₂) (h : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂) :
    ¬ M.IsAlphaCut v v₂ x₁ x₂ := by
  classical
  set K := M.cut v v₂ x₁ x₂ with hK
  have hKat : K.atoms = insert v₂ M.atoms := rfl
  have hvK : v ∈ K.atoms := by rw [hKat]; exact mem_insert_of_mem hc.1
  have hv₂K : v₂ ∈ K.atoms := by rw [hKat]; exact mem_insert_self _ _
  have h2 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨v, hc.1⟩ hconn
  unfold Molecule.IsAlphaCut
  rw [← hK, h2, Degen.numComponents_eq_card_componentSets, not_le]
  have hne : Degen.componentSet K v ≠ Degen.componentSet K v₂ := fun he =>
    h ((Degen.componentSet_eq_iff K hvK).mp he)
  have hsub : ({Degen.componentSet K v, Degen.componentSet K v₂} : Finset (Finset V)) ⊆ Degen.componentSets K := by
    intro S hS
    unfold Degen.componentSets
    rcases mem_insert.mp hS with rfl | hS
    · exact mem_image_of_mem _ hvK
    · rw [mem_singleton.mp hS]; exact mem_image_of_mem _ hv₂K
  have := card_le_card hsub
  rw [card_pair hne] at this
  omega


/-- **Lifting a cut through the erasure of `K0`.** A cut of `N = M ∖ K0` whose new atom is separated from `v`, and
whose component of `v` consists of atoms with no lost dart, is a cut of `M` with the same property. -/
theorem cut_lift_erase (M : Molecule V D) (K0 : Finset V) {v v₂ v₂' : V}
    {x₁ x₂ : Degen.RetainedDart M K0} (hc : (Degen.eraseAtoms M K0).IsCutData v v₂ x₁ x₂)
    (hsep : ¬ ((Degen.eraseAtoms M K0).cut v v₂ x₁ x₂).SameComponent v v₂)
    (hdeg : ∀ u ∈ (Degen.eraseAtoms M K0).atoms, ((Degen.eraseAtoms M K0).cut v v₂ x₁ x₂).SameComponent v u →
      u ≠ v → (Degen.eraseAtoms M K0).deg u = M.deg u)
    (hv₂' : v₂' ∉ M.atoms) :
    M.IsCutData v v₂' x₁.val x₂.val ∧ ¬ (M.cut v v₂' x₁.val x₂.val).SameComponent v v₂' := by
  classical
  set N := Degen.eraseAtoms M K0 with hN
  set KN := N.cut v v₂ x₁ x₂ with hKN
  set KM := M.cut v v₂' x₁.val x₂.val with hKM
  have hvN : v ∈ M.atoms \ K0 := hc.1
  have hcM : M.IsCutData v v₂' x₁.val x₂.val :=
    ⟨(mem_sdiff.mp hvN).1, hv₂', hc.2.2.1, hc.2.2.2.1, fun h => hc.2.2.2.2.1 (Subtype.ext h),
      hc.2.2.2.2.2.1, hc.2.2.2.2.2.2⟩
  refine ⟨hcM, ?_⟩
  have hKNat : KN.atoms = insert v₂ N.atoms := rfl
  set S : Finset V := KN.atoms.filter (fun u => KN.SameComponent v u) with hS
  have hvS : v ∈ S := mem_filter.mpr ⟨by rw [hKNat]; exact mem_insert_of_mem hc.1, Relation.EqvGen.refl _⟩
  have hv₂S : v₂ ∉ S := fun h => hsep (mem_filter.mp h).2
  have hSN : ∀ u ∈ S, u ≠ v₂ → u ∈ N.atoms := by
    intro u hu hne
    have := (mem_filter.mp hu).1
    rw [hKNat] at this
    exact (mem_insert.mp this).resolve_left hne
  have hv₂'S : v₂' ∉ S := by
    intro h
    by_cases he : v₂' = v₂
    · exact hv₂S (he ▸ h)
    · have := hSN _ h he
      exact hv₂' (mem_sdiff.mp this).1
  have hSclosed : ∀ z : Degen.RetainedDart M K0, KN.atom z ∈ S → KN.atom (KN.mate z) ∈ S := by
    intro z hz
    obtain ⟨hzA, hzS⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨KN.atom_mem _, ?_⟩
    exact Relation.EqvGen.trans _ _ _ hzS (Relation.EqvGen.rel _ _ ⟨z, rfl, rfl⟩)
  have hclosed : ∀ z : D, KM.atom z ∈ S → KM.atom (KM.mate z) ∈ S := by
    intro z hz
    have hKMz : KM.atom z = if (M.atom z = v ∧ z ≠ x₁.val ∧ z ≠ x₂.val) then v₂' else M.atom z := rfl
    by_cases hcond : M.atom z = v ∧ z ≠ x₁.val ∧ z ≠ x₂.val
    · rw [hKMz, if_pos hcond] at hz; exact absurd hz hv₂'S
    rw [hKMz, if_neg hcond] at hz
    have huN : M.atom z ∈ N.atoms := hSN _ hz (fun h => hv₂S (h ▸ hz))
    have huK0 : M.atom z ∉ K0 := (mem_sdiff.mp huN).2
    have hKMm : KM.atom (KM.mate z) = if (M.atom (M.mate z) = v ∧ M.mate z ≠ x₁.val ∧ M.mate z ≠ x₂.val)
        then v₂' else M.atom (M.mate z) := rfl
    by_cases hret : M.atom (M.mate z) ∉ K0
    · set zr : Degen.RetainedDart M K0 := ⟨z, huK0, hret⟩ with hzr
      have hKNz : KN.atom zr = M.atom z := by
        change (if (M.atom z = v ∧ zr ≠ x₁ ∧ zr ≠ x₂) then v₂ else M.atom z) = _
        rw [if_neg]
        rintro ⟨h1, h2, h3⟩
        exact hcond ⟨h1, fun h => h2 (Subtype.ext h), fun h => h3 (Subtype.ext h)⟩
      have hcl := hSclosed zr (by rw [hKNz]; exact hz)
      have hKNm : KN.atom (KN.mate zr) = if (M.atom (M.mate z) = v ∧ (⟨M.mate z, by
          have := zr.2; rw [M.mate_mate]; exact ⟨hret, huK0⟩⟩ : Degen.RetainedDart M K0) ≠ x₁ ∧
          (⟨M.mate z, by have := zr.2; rw [M.mate_mate]; exact ⟨hret, huK0⟩⟩ : Degen.RetainedDart M K0) ≠ x₂)
          then v₂ else M.atom (M.mate z) := rfl
      by_cases hc' : M.atom (M.mate z) = v ∧ M.mate z ≠ x₁.val ∧ M.mate z ≠ x₂.val
      · rw [hKNm, if_pos ⟨hc'.1, fun h => hc'.2.1 (congrArg Subtype.val h), fun h => hc'.2.2 (congrArg Subtype.val h)⟩] at hcl
        exact absurd hcl hv₂S
      · rw [hKMm, if_neg hc']
        rw [hKNm, if_neg (by
          rintro ⟨h1, h2, h3⟩
          exact hc' ⟨h1, fun h => h2 (Subtype.ext h), fun h => h3 (Subtype.ext h)⟩)] at hcl
        exact hcl
    · push Not at hret
      exfalso
      by_cases huv : M.atom z = v
      · have hz' : z = x₁.val ∨ z = x₂.val := by
          by_contra hn; push Not at hn; exact hcond ⟨huv, hn.1, hn.2⟩
        rcases hz' with rfl | rfl
        · exact x₁.2.2 hret
        · exact x₂.2.2 hret
      · have hd := hdeg _ huN (mem_filter.mp hz).2 huv
        have h1 := deg_eraseAtoms_add (N := M) K0 huK0
        have h2 : 1 ≤ (Degen.removedDartsAt M K0 (M.atom z)).card :=
          card_pos.mpr ⟨z, by unfold Degen.removedDartsAt; simp [Molecule.dartsAt, hret]⟩
        rw [hN] at hd
        omega
  intro hsame
  have := (mem_iff_of_sameComponent_of_closed hclosed hsame).mp hvS
  exact hv₂'S this

end
end WaveTurbulence.FinalCountG8
