/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5c
public import WaveTurbulence.Foundations.FinalCount.G3Iso
public import WaveTurbulence.Foundations.FinalCount.G3MapBase
public import WaveTurbulence.Foundations.FinalCount.G3ClDev1
/-! **FINALCOUNT-G3 (R29 UNTOUCHED-ISO).**  A component of the input state without tame atoms (`TameFree`), with at least one bond, is
isomorphic (`DartIso`, atoms fixed) to the component of the same atom after Operation 5.  Together with `Op5.perfect_tameFree`
this is the isomorphism `perfect component after Op 5 ≅ its component at the Ops 1-4 state`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {Tm : V → Prop}

section iso
variable {h : HSt V D₀}

/-- In a tame-free component of the input, no atom is tame. -/
theorem tameFree_notin {a b : V} (hT : TameFree h Tm a)
    (hsc : h.s.M.SameComponent a b) : b ∉ tameSet h Tm := by
  intro hb
  have hb' := tameSet_mem.1 hb
  exact hT b hb'.1 hsc hb'.2.1 hb'.2.2

theorem iso_or_pos {M : Molecule V D₀} {a b : V} (hsc : M.SameComponent a b) :
    a = b ∨ (1 ≤ M.deg a ∧ 1 ≤ M.deg b) := by
  induction hsc with
  | rel x y hr =>
    obtain ⟨z, h1, h2⟩ := hr
    right
    refine ⟨Finset.card_pos.2 ⟨z, by simp [Molecule.dartsAt, h1]⟩,
      Finset.card_pos.2 ⟨M.mate z, by simp [Molecule.dartsAt, h2]⟩⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih => rcases ih with rfl | ⟨h1, h2⟩; exacts [Or.inl rfl, Or.inr ⟨h2, h1⟩]
  | trans x y z _ _ ih1 ih2 =>
    rcases ih1 with rfl | ⟨h1, h2⟩
    · exact ih2
    · rcases ih2 with rfl | ⟨h3, h4⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h4⟩

theorem op5_sc_lift {x y : V} (hsc : (restrictP (eraseSet h.s.M (tameSet h Tm)) (keepS h.s (tameSet h Tm))
    (keepS_closed h.s (tameSet h Tm))).SameComponent x y) : h.s.M.SameComponent x y := by
  induction hsc with
  | rel u v hr =>
    obtain ⟨z, h1, h2⟩ := hr
    exact Relation.EqvGen.rel _ _ ⟨z.1.1, h1, h2⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Every atom of a tame-free component with a bond survives Operation 5, in the same component. -/
theorem op5_comp {a b : V} (hT : TameFree h Tm a) (ha5 : a ∈ (h.op5 Tm).s.M.atoms)
    (hsc : h.s.M.SameComponent a b) :
    b ∈ (h.op5 Tm).s.M.atoms ∧ (h.op5 Tm).s.M.SameComponent a b := by
  set T := tameSet h Tm with hTdef
  have haM : a ∈ h.s.M.atoms := (Op5.atoms_sub ha5).1
  have hbM : b ∈ h.s.M.atoms := by
    rcases iso_or_pos hsc with rfl | ⟨-, hb⟩
    · exact haM
    · by_contra hn
      have : h.s.M.deg b = 0 := by
        unfold Molecule.deg
        rw [Finset.card_eq_zero]
        ext x
        simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hx; exact hn (hx ▸ h.s.M.atom_mem x)
      omega
  have hbT : b ∉ T := tameFree_notin hT hsc
  have hdeg : 1 ≤ (eraseSet h.s.M T).deg b := by
    have hk := (Finset.mem_filter.1 ha5).2
    have ha1 : 1 ≤ (eraseSet h.s.M T).deg a := hk
    have haT : a ∉ T := tameFree_notin hT (Relation.EqvGen.refl _)
    have hdc := eraseSet_deg_card h.s.M T haT
    -- multiplicity at b is zero: all its neighbours lie in the component
    have hmult : ∀ c : V, h.s.M.SameComponent a c → multS h.s.M T c = 0 := by
      intro c hc
      unfold multS
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hxT
      have hxc : h.s.M.atom x = c := by simpa [Molecule.dartsAt] using hx
      have hsc' : h.s.M.SameComponent a (h.s.M.atom (h.s.M.mate x)) :=
        Relation.EqvGen.trans _ _ _ hc (Relation.EqvGen.rel _ _ ⟨x, hxc, rfl⟩)
      exact tameFree_notin hT hsc' hxT
    rcases iso_or_pos hsc with rfl | ⟨h1, h2⟩
    · exact ha1
    · have := eraseSet_deg_card h.s.M T hbT
      have := hmult b hsc
      omega
  have hkb : keepS h.s T b := hdeg
  have hb5 : b ∈ (h.op5 Tm).s.M.atoms := Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hbM, hbT⟩, hkb⟩
  refine ⟨hb5, ?_⟩
  have hsN : (eraseSet h.s.M T).SameComponent a b := by
    refine scS_avoid hsc ?_
    rintro ⟨k, hk, hkc⟩
    exact tameFree_notin hT hkc hk
  exact restrictP_sc_of (eraseSet h.s.M T) (keepS h.s T) (keepS_closed h.s T) hsN (Finset.mem_filter.1 ha5).2

theorem op5_compAtoms {a : V} (hT : TameFree h Tm a) (ha5 : a ∈ (h.op5 Tm).s.M.atoms) :
    compAtoms (h.op5 Tm).s.M a = compAtoms h.s.M a := by
  ext b
  unfold compAtoms
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hb, hsc⟩
    exact ⟨(Op5.atoms_sub hb).1, op5_sc_lift hsc⟩
  · rintro ⟨hb, hsc⟩
    exact op5_comp hT ha5 hsc


/-- The dart bijection. -/
def untouchedEquiv {a : V} (hT : TameFree h Tm a) (ha5 : a ∈ (h.op5 Tm).s.M.atoms) :
    PDart h.s.M (compP h.s.M a) ≃ PDart (h.op5 Tm).s.M (compP (h.op5 Tm).s.M a) where
  toFun x :=
    ⟨⟨⟨x.1, tameFree_notin hT x.2, tameFree_notin hT (Relation.EqvGen.trans _ _ _ x.2
        (Relation.EqvGen.rel _ _ ⟨x.1, rfl, rfl⟩))⟩,
      by
        show 1 ≤ (eraseSet h.s.M (tameSet h Tm)).deg _
        unfold Molecule.deg
        exact Finset.card_pos.2 ⟨⟨x.1, tameFree_notin hT x.2, tameFree_notin hT (Relation.EqvGen.trans _ _ _ x.2
          (Relation.EqvGen.rel _ _ ⟨x.1, rfl, rfl⟩))⟩, by simp [Molecule.dartsAt]; rfl⟩⟩,
      (op5_comp hT ha5 x.2).2⟩
  invFun y := ⟨y.1.1.1, op5_sc_lift y.2⟩
  left_inv x := rfl
  right_inv y := rfl

/-- **UNTOUCHED-ISO**: the component of a tame-free atom is unchanged by Operation 5. -/
def untouchedIso {a : V} (hT : TameFree h Tm a) (ha5 : a ∈ (h.op5 Tm).s.M.atoms) :
    DartIso (compMol h.s.M a) (compMol (h.op5 Tm).s.M a) where
  e := untouchedEquiv hT ha5
  atoms := op5_compAtoms hT ha5
  atom := fun x => rfl
  mate := fun x => rfl
  out := fun x => rfl

/-- The iso respects `down`. -/
theorem untouchedIso_down {a : V} (hT : TameFree h Tm a) (ha5 : a ∈ (h.op5 Tm).s.M.atoms)
    (x : PDart h.s.M (compP h.s.M a)) :
    (h.op5 Tm).s.down (untouchedEquiv hT ha5 x).1 = h.s.down x.1 := rfl

end iso
end WaveTurbulence.FinalCountG3
