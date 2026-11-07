/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCIso
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
/-! # VINE-COUNT part 26: a hyper object is a vine cut of its adjoint.

For `K : VineCut M` whose object is `.hyper R` (an adjoint VC after deleting the bond `R.added` between the joints),
`adjointCut` is the same cut data seen in `eraseBond M R.added`, where the object is an ordinary VC (a block with its
chain), with no change of atoms, joints and cut darts.  The doubly cut molecules have the same atoms for the same
darts, so the removed vines are related by a bijection of darts (`VCIso`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
  {M : Molecule V D} (K : VineCut M) (R : HyperLikeRealization M K.C.atoms K.C.upper K.C.lower)
  (h : K.C.shape = .hyper R)

include h in
theorem contains_hyper {x : D} (hx : K.C.ContainsDart x) :
    x ≠ R.added ∧ x ≠ M.mate R.added ∧ M.InGroup K.C.atoms x := by
  unfold Object.ContainsDart at hx
  rw [h] at hx
  exact hx

section EraseCut
variable (e : D)

theorem erase_cut_atom (v v₂ : V) (x₁ x₂ : D) (h1 : x₁ ≠ e ∧ x₁ ≠ M.mate e) (h2 : x₂ ≠ e ∧ x₂ ≠ M.mate e)
    (y : {x : D // x ≠ e ∧ x ≠ M.mate e}) :
    ((Molecule.eraseBond M e).cut v v₂ ⟨x₁, h1⟩ ⟨x₂, h2⟩).atom y = (M.cut v v₂ x₁ x₂).atom y.1 := by
  rw [cut_atom, cut_atom]
  have e1 : (y ≠ ⟨x₁, h1⟩) ↔ y.1 ≠ x₁ := by simp [Subtype.ext_iff]
  have e2 : (y ≠ ⟨x₂, h2⟩) ↔ y.1 ≠ x₂ := by simp [Subtype.ext_iff]
  simp only [e1, e2]
  rfl

theorem erase_cut_cut_atom (v v₂ v' v₂' : V) (x₁ x₂ y₁ y₂ : D) (h1 : x₁ ≠ e ∧ x₁ ≠ M.mate e)
    (h2 : x₂ ≠ e ∧ x₂ ≠ M.mate e) (g1 : y₁ ≠ e ∧ y₁ ≠ M.mate e) (g2 : y₂ ≠ e ∧ y₂ ≠ M.mate e)
    (y : {x : D // x ≠ e ∧ x ≠ M.mate e}) :
    (((Molecule.eraseBond M e).cut v v₂ ⟨x₁, h1⟩ ⟨x₂, h2⟩).cut v' v₂' ⟨y₁, g1⟩ ⟨y₂, g2⟩).atom y =
      ((M.cut v v₂ x₁ x₂).cut v' v₂' y₁ y₂).atom y.1 := by
  rw [cut_atom ((Molecule.eraseBond M e).cut v v₂ ⟨x₁, h1⟩ ⟨x₂, h2⟩), cut_atom (M.cut v v₂ x₁ x₂),
    erase_cut_atom e v v₂ x₁ x₂ h1 h2 y]
  have e1 : (y ≠ ⟨y₁, g1⟩) ↔ y.1 ≠ y₁ := by simp [Subtype.ext_iff]
  have e2 : (y ≠ ⟨y₂, g2⟩) ↔ y.1 ≠ y₂ := by simp [Subtype.ext_iff]
  simp only [e1, e2]

end EraseCut

include h in
theorem adj_x₁ : K.x₁ ≠ R.added ∧ K.x₁ ≠ M.mate R.added :=
  ⟨(contains_hyper K R h K.in_a.1).1, (contains_hyper K R h K.in_a.1).2.1⟩
include h in
theorem adj_x₂ : K.x₂ ≠ R.added ∧ K.x₂ ≠ M.mate R.added :=
  ⟨(contains_hyper K R h K.in_a.2).1, (contains_hyper K R h K.in_a.2).2.1⟩
include h in
theorem adj_y₁ : K.y₁ ≠ R.added ∧ K.y₁ ≠ M.mate R.added :=
  ⟨(contains_hyper K R h K.in_b.1).1, (contains_hyper K R h K.in_b.1).2.1⟩
include h in
theorem adj_y₂ : K.y₂ ≠ R.added ∧ K.y₂ ≠ M.mate R.added :=
  ⟨(contains_hyper K R h K.in_b.2).1, (contains_hyper K R h K.in_b.2).2.1⟩

include h in
/-- **The hyper object as a vine cut of its adjoint** `eraseBond M R.added`. -/
def adjointCut : VineCut (Molecule.eraseBond M R.added) where
  C := ⟨K.C.atoms, K.C.upper, K.C.lower, .vc R.adjoint⟩
  fa := K.fa
  fb := K.fb
  x₁ := ⟨K.x₁, adj_x₁ K R h⟩
  x₂ := ⟨K.x₂, adj_x₂ K R h⟩
  y₁ := ⟨K.y₁, adj_y₁ K R h⟩
  y₂ := ⟨K.y₂, adj_y₂ K R h⟩
  a_mem := K.a_mem
  b_mem := K.b_mem
  ab_ne := K.ab_ne
  cut_a := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := K.cut_a
    exact ⟨h1, h2, h3, h4, fun e => h5 (congrArg Subtype.val e), h6, h7⟩
  cut_b := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := K.cut_b
    refine ⟨h1, h2, ?_, ?_, ?_, h6, h7⟩
    · rw [erase_cut_atom R.added K.C.upper K.fa K.x₁ K.x₂ (adj_x₁ K R h) (adj_x₂ K R h)]; exact h3
    · rw [erase_cut_atom R.added K.C.upper K.fa K.x₁ K.x₂ (adj_x₁ K R h) (adj_x₂ K R h)]; exact h4
    · intro e; exact h5 (congrArg Subtype.val e)
  in_a := ⟨(contains_hyper K R h K.in_a.1).2.2, (contains_hyper K R h K.in_a.2).2.2⟩
  in_b := ⟨(contains_hyper K R h K.in_b.1).2.2, (contains_hyper K R h K.in_b.2).2.2⟩
  closed := by
    intro y hy
    have key := K.closed y.1
    rw [erase_cut_cut_atom R.added K.C.upper K.fa K.C.lower K.fb K.x₁ K.x₂ K.y₁ K.y₂ (adj_x₁ K R h) (adj_x₂ K R h) (adj_y₁ K R h) (adj_y₂ K R h) y] at hy
    have := key hy
    have e3 := erase_cut_cut_atom R.added K.C.upper K.fa K.C.lower K.fb K.x₁ K.x₂ K.y₁ K.y₂ (adj_x₁ K R h) (adj_x₂ K R h) (adj_y₁ K R h) (adj_y₂ K R h)
      (Molecule.mate (Molecule.eraseBond M R.added) y)
    exact e3 ▸ this


section Rel
/-- The doubly cut molecules of `K` and of its adjoint cut give the same atom to a dart of the adjoint. -/
theorem adj_cutMol_atom (y : {x : D // x ≠ R.added ∧ x ≠ M.mate R.added}) :
    (adjointCut K R h).cutMol.atom y = K.cutMol.atom y.1 :=
  erase_cut_cut_atom R.added K.C.upper K.fa K.C.lower K.fb K.x₁ K.x₂ K.y₁ K.y₂ (adj_x₁ K R h) (adj_x₂ K R h)
    (adj_y₁ K R h) (adj_y₂ K R h) y

include h in
/-- Darts at the joints other than the four cut darts end up at the fresh atoms. -/
theorem cutMol_atom_joint {z : D} (hz1 : z ≠ K.x₁) (hz2 : z ≠ K.x₂) (hz3 : z ≠ K.y₁) (hz4 : z ≠ K.y₂)
    (hz : M.atom z = K.C.upper ∨ M.atom z = K.C.lower) : K.cutMol.atom z ∉ K.C.atoms := by
  have hab := K.ab_ne
  show ((M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).atom z ∉ K.C.atoms
  rw [cut_atom (M.cut K.C.upper K.fa K.x₁ K.x₂), cut_atom M]
  rcases hz with hz | hz
  · rw [if_pos (show M.atom z = K.C.upper ∧ z ≠ K.x₁ ∧ z ≠ K.x₂ from ⟨hz, hz1, hz2⟩)]
    rw [if_neg (fun hh : K.fa = K.C.lower ∧ z ≠ K.y₁ ∧ z ≠ K.y₂ => K.fa_ne_b hh.1)]
    exact fun hh => K.fa_fresh (objectAtoms_sub K.C hh)
  · have hin : (if M.atom z = K.C.upper ∧ z ≠ K.x₁ ∧ z ≠ K.x₂ then K.fa else M.atom z) = M.atom z :=
      if_neg (fun hh => hab (hh.1.symm.trans hz))
    rw [hin, if_pos (show M.atom z = K.C.lower ∧ z ≠ K.y₁ ∧ z ≠ K.y₂ from ⟨hz, hz3, hz4⟩)]
    exact fun hh => K.fb_fresh (objectAtoms_sub K.C hh)

include h in
theorem added_atom_joint : M.atom R.added = K.C.upper ∨ M.atom R.added = K.C.lower := by
  have e := R.ends_eq
  unfold Molecule.ends at e
  rcases Sym2.eq_iff.mp e with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

include h in
theorem added_mate_atom_joint : M.atom (M.mate R.added) = K.C.upper ∨ M.atom (M.mate R.added) = K.C.lower := by
  have e := R.ends_eq
  unfold Molecule.ends at e
  rcases Sym2.eq_iff.mp e with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr h1
  · exact Or.inl h1

include h in
theorem cutMol_atom_added : K.cutMol.atom R.added ∉ K.C.atoms :=
  cutMol_atom_joint K R h (adj_x₁ K R h).1.symm (adj_x₂ K R h).1.symm (adj_y₁ K R h).1.symm (adj_y₂ K R h).1.symm
    (added_atom_joint K R h)

include h in
theorem cutMol_atom_added_mate : K.cutMol.atom (M.mate R.added) ∉ K.C.atoms :=
  cutMol_atom_joint K R h (adj_x₁ K R h).2.symm (adj_x₂ K R h).2.symm (adj_y₁ K R h).2.symm (adj_y₂ K R h).2.symm
    (added_mate_atom_joint K R h)

end Rel

end WaveTurbulence.VineCount
