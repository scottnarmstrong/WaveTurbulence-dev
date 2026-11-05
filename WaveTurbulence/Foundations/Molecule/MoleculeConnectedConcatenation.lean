/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockRealizations
import Mathlib.Tactic

/-! # Connected realizations are preserved by actual concatenation -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] (M : Molecule V D)

/-- Two connected groups sharing an atom have a connected actual union. -/
theorem groupConnected_union {A B : Finset V} {c : V} (hA : GroupConnected M A)
    (hB : GroupConnected M B) (hcA : c ∈ A) (hcB : c ∈ B) : GroupConnected M (A ∪ B) := by
  have hanchor : ∀ u ∈ A ∪ B, (induced M (A ∪ B)).SameComponent u c := by
    intro u hu
    rcases Finset.mem_union.mp hu with huA | huB
    · exact induced_path_mono M Finset.subset_union_left (hA.2 u huA c hcA)
    · exact induced_path_mono M Finset.subset_union_right (hB.2 u huB c hcB)
  refine ⟨⟨c,Finset.mem_union_left B hcA⟩,?_⟩
  intro u hu z hz
  exact sameComponent_trans (induced M (A ∪ B)) (hanchor u hu)
    (sameComponent_symm (induced M (A ∪ B)) (hanchor z hz))

omit [DecidableEq V] in
/-- Deleting an external bond preserves every path inside a group. -/
theorem eraseBond_external_path (e : D) {S : Finset V} (hne : ¬ M.InGroup S e) {u v : V}
    (hp : (induced M S).SameComponent u v) : (induced (eraseBond M e) S).SameComponent u v := by
  induction hp with
  | rel a b hab =>
    obtain ⟨⟨x,hxa,hxb⟩,haS,hbS⟩ := (induced_adj_iff M S a b).mp hab
    have hxg : M.InGroup S x := ⟨hxa.symm ▸ haS,hxb.symm ▸ hbS⟩
    have hx1 : x ≠ e := fun he => hne (he ▸ hxg)
    have hx2 : x ≠ M.mate e := by
      intro he
      have hg : M.InGroup S (M.mate e) := he ▸ hxg
      exact hne ⟨by simpa only [M.mate_mate] using hg.2,hg.1⟩
    apply Relation.EqvGen.rel
    exact (induced_adj_iff (eraseBond M e) S a b).mpr ⟨⟨⟨x,hx1,hx2⟩,hxa,hxb⟩,haS,hbS⟩
  | refl => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact sameComponent_symm (induced (eraseBond M e) S) ih
  | trans a b c hab hbc ihab ihbc => exact sameComponent_trans (induced (eraseBond M e) S) ihab ihbc

omit [DecidableEq V] in
/-- Thus the whole group remains connected when the deleted bond is external. -/
theorem eraseBond_external_connected (e : D) {S : Finset V} (hne : ¬ M.InGroup S e)
    (hc : GroupConnected M S) : GroupConnected (eraseBond M e) S :=
  ⟨hc.1,fun u hu v hv => eraseBond_external_path M e hne (hc.2 u hu v hv)⟩

variable [Fintype D] [DecidableEq D]

/-- Concatenation yields a connected block, or a hyper-block with an actual
connected adjoint realization, so the result can be reused in the overlap API. -/
theorem blocks_concatenate_connected (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (hA : M.IsBlock A a c) (hB : M.IsBlock B b c)
    (hcA : GroupConnected M A) (hcB : GroupConnected M B) (hi : A ∩ B = {c}) :
    Nonempty (BlockRealization M (A ∪ B) a b) := by
  rcases blocks_concatenate M hM hA hB hcA hi with hU | ⟨e,he,hU⟩
  · exact ⟨.block hU (groupConnected_union M hcA hcB hA.2.2.1 hB.2.2.1)⟩
  · have haB : a ∉ B := by
      intro haB
      have hh : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨hA.2.1,haB⟩
      rw [hi] at hh
      exact hA.2.2.2.1 (Finset.mem_singleton.mp hh)
    have hbA : b ∉ A := by
      intro hbA
      have hh : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hbA,hB.2.1⟩
      rw [hi] at hh
      exact hB.2.2.2.1 (Finset.mem_singleton.mp hh)
    have hend : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨
        (M.atom e = b ∧ M.atom (M.mate e) = a) := Sym2.eq_iff.mp he
    have hnotA : ¬ M.InGroup A e := by
      intro hg
      rcases hend with hh | hh
      · exact hbA (hh.2 ▸ hg.2)
      · exact hbA (hh.1 ▸ hg.1)
    have hnotB : ¬ M.InGroup B e := by
      intro hg
      rcases hend with hh | hh
      · exact haB (hh.1 ▸ hg.1)
      · exact haB (hh.2 ▸ hg.2)
    have hcE := groupConnected_union (eraseBond M e)
      (eraseBond_external_connected M e hnotA hcA) (eraseBond_external_connected M e hnotB hcB)
      hA.2.2.1 hB.2.2.1
    exact ⟨.hyper e he hU hcE⟩

end WaveTurbulence.Mole
