/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineObj4
public import WaveTurbulence.Foundations.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
/-! **FINALCOUNT-G3: `vineLG`, part 2: darts of a final vine component seen in `M_sub`.** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem anc_mem_group {b : V} (hb : b ∈ hf.s.M.atoms) (hc : hf.s.M.SameComponent a₀ b) :
    hf.anc b ∈ AncGroup hf a₀ :=
  Finset.mem_image.2 ⟨b, (mem_compMol _ _).2 ⟨hb, hc⟩, rfl⟩

/-- Darts of the component lie in the group of `M_sub` formed by the ancestors. -/
theorem inGroup_down (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) (x : hf.s.D)
    (hx : hf.s.M.SameComponent a₀ (hf.s.M.atom x)) : M₀.InGroup (AncGroup hf a₀) (hf.s.down x) := by
  refine ⟨?_, ?_⟩
  · rw [hA.atom]; exact anc_mem_group (hf.s.M.atom_mem x) hx
  · rw [hD.mate, hA.atom]
    exact anc_mem_group (hf.s.M.atom_mem _)
      (Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩))

/-- Two distinct non-mate darts at a joint of degree `2`. -/
theorem joint_two_darts (hnl : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) {j : V}
    (hd : hf.s.M.deg j = 2) : ∃ x y : hf.s.D, hf.s.M.atom x = j ∧ hf.s.M.atom y = j ∧ x ≠ y ∧ y ≠ hf.s.M.mate x ∧
      ∀ z : hf.s.D, hf.s.M.atom z = j → z = x ∨ z = y := by
  have hc : (hf.s.M.dartsAt j).card = 2 := hd
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 hc
  have hx : x ∈ hf.s.M.dartsAt j := by rw [hs]; simp
  have hy : y ∈ hf.s.M.dartsAt j := by rw [hs]; simp
  have hx' := (Finset.mem_filter.1 hx).2
  have hy' := (Finset.mem_filter.1 hy).2
  refine ⟨x, y, hx', hy', hxy, fun e => hnl x ?_, fun z hz => ?_⟩
  · rw [← e, hx', hy']
  · have : z ∈ hf.s.M.dartsAt j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
    rw [hs] at this; simpa using this

theorem contains_of (U : Object M₀) (z : D₀) (hg : M₀.InGroup U.atoms z)
    (hn : ∀ R, U.shape = VineLikeObject.hyper R → z ≠ R.added ∧ z ≠ M₀.mate R.added) : U.ContainsDart z := by
  unfold Object.ContainsDart
  rcases hsh : U.shape with hvc | R'
  · exact hg
  · exact ⟨(hn R' hsh).1, (hn R' hsh).2, hg⟩

/-- **Use 1 (Step 1 removes the collection).**  An object of `M_sub` whose atom set contains the ancestor group of a final vine
component contains a dart that is the image of a final dart. -/
theorem final_dart_contained (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hnl : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) (U : Object M₀)
    (hU : AncGroup hf a₀ ⊆ U.atoms) : ∃ x : hf.s.D, U.ContainsDart (hf.s.down x) := by
  obtain ⟨x, y, hx, hy, hxy, hym, -⟩ := joint_two_darts hnl J.d1
  have gx : M₀.InGroup U.atoms (hf.s.down x) := by
    have := inGroup_down hA hD x (by rw [hx]; exact J.c1)
    exact ⟨hU this.1, hU this.2⟩
  have gy : M₀.InGroup U.atoms (hf.s.down y) := by
    have := inGroup_down hA hD y (by rw [hy]; exact J.c1)
    exact ⟨hU this.1, hU this.2⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ z : hf.s.D, M₀.InGroup U.atoms (hf.s.down z) → ¬ U.ContainsDart (hf.s.down z) →
      ∃ R, U.shape = VineLikeObject.hyper R ∧ (hf.s.down z = R.added ∨ hf.s.down z = M₀.mate R.added) := by
    intro z gz hn
    by_contra h'
    push Not at h'
    exact hn (contains_of U _ gz fun R hR => h' R hR)
  obtain ⟨R1, h1, e1⟩ := key x gx (hcon x)
  obtain ⟨R2, h2, e2⟩ := key y gy (hcon y)
  have hR : R1 = R2 := by
    have := h1.symm.trans h2
    exact VineLikeObject.hyper.inj this
  subst hR
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact hxy (hA.inj (e1.trans e2.symm))
  · exact hym (hA.inj (by rw [e2, ← hD.mate, e1]))
  · exact hym (hA.inj (by rw [← hD.mate, e1, M₀.mate_mate, e2]))
  · exact hxy (hA.inj (e1.trans e2.symm))

/-- The darts of the group `AncGroup` at the ancestor of a joint (of degree `2`) are the images of the two final darts at the joint,
provided the group has internal degree `≤ 2` there. -/
theorem group_darts_joint (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hnl : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) {j : V} (hj : j ∈ hf.s.M.atoms)
    (hc : hf.s.M.SameComponent a₀ j) (hd : hf.s.M.deg j = 2) (hdeg : M₀.degIn (AncGroup hf a₀) (hf.anc j) ≤ 2) :
    ∀ z, M₀.atom z = hf.anc j → M₀.InGroup (AncGroup hf a₀) z →
      ∃ x : hf.s.D, hf.s.M.atom x = j ∧ hf.s.down x = z := by
  obtain ⟨x, y, hx, hy, hxy, hym, hall⟩ := joint_two_darts hnl hd
  have gx : M₀.InGroup (AncGroup hf a₀) (hf.s.down x) := inGroup_down hA hD x (by rw [hx]; exact hc)
  have gy : M₀.InGroup (AncGroup hf a₀) (hf.s.down y) := inGroup_down hA hD y (by rw [hy]; exact hc)
  have ax : M₀.atom (hf.s.down x) = hf.anc j := by rw [hA.atom, hx]
  have ay : M₀.atom (hf.s.down y) = hf.anc j := by rw [hA.atom, hy]
  set F := (M₀.dartsAt (hf.anc j)).filter (M₀.InGroup (AncGroup hf a₀)) with hF
  have hsub : ({hf.s.down x, hf.s.down y} : Finset D₀) ⊆ F := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.2 ⟨(Mole.mem_dartsAt M₀ _ _).2 ax, gx⟩
    · exact Finset.mem_filter.2 ⟨(Mole.mem_dartsAt M₀ _ _).2 ay, gy⟩
  have hne : hf.s.down x ≠ hf.s.down y := fun e => hxy (hA.inj e)
  have hcard : F.card ≤ ({hf.s.down x, hf.s.down y} : Finset D₀).card := by
    rw [Finset.card_pair hne]; exact hdeg
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro z hz1 hz2
  have : z ∈ F := Finset.mem_filter.2 ⟨(Mole.mem_dartsAt M₀ _ _).2 hz1, hz2⟩
  rw [← heq] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl
  · exact ⟨x, hx, rfl⟩
  · exact ⟨y, hy, rfl⟩

end WaveTurbulence.FinalCountG3
