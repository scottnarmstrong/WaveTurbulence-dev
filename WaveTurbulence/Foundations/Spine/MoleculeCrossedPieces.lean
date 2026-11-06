/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeCrossedIntersection
import Mathlib.Tactic

/-!
# The exterior blocks in the interleaving decomposition

DH23 Lemma 4.11(2). The middle block is A∩B; the left exterior block is
(A\B)∪{b1}. Its shared joint has one incoming and one outgoing incidence
because the full old atom splits into two balanced joint pairs.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- The actual exterior piece in the crossed-joint configuration is a
block, including the exact orientation counts at its two new joints. -/
theorem crossed_left_piece_isBlock (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (hA : M.IsBlock A a1 a2) (hB : M.IsBlock B b1 b2) (hcB : GroupConnected M B)
    (ha1B : a1 ∈ B) (ha11 : a1 ≠ b1) (ha12 : a1 ≠ b2)
    (hb1A : b1 ∈ A) (hb11 : b1 ≠ a1) (hb12 : b1 ≠ a2)
    (ha2out : a2 ∉ B) (hb2out : b2 ∉ A) :
    M.IsBlock ((A \ B) ∪ {b1}) a2 b1 := by
  let C := (A \ B) ∪ {b1}
  let Q := A ∩ B
  have hQ : M.IsBlock Q a1 b1 := crossed_intersection_isBlock M hM hA hB
    ha1B ha11 ha12 hb1A hb11 hb12 ha2out hb2out
  have hsub : C ⊆ A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzB
    · exact (Finset.mem_sdiff.mp hzP).1
    · exact (Finset.mem_singleton.mp hzB).symm ▸ hb1A
  have hb1C : b1 ∈ C := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hb1Q : b1 ∈ Q := Finset.mem_inter.mpr ⟨hb1A,hB.2.1⟩
  have ha2P : a2 ∈ A \ B := Finset.mem_sdiff.mpr ⟨hA.2.2.1,ha2out⟩
  have ha2C : a2 ∈ C := Finset.mem_union_left _ ha2P
  have hcover : C ∪ Q = A := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [C,Q,hb1A,hB.2.1]
    · simp only [C,Q,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have hinter : C ∩ Q = {b1} := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [C,Q,hb1A,hB.2.1]
    · simp only [C,Q,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have hno : ∀ x, M.atom x = b1 → M.atom (M.mate x) ≠ b1 := by
    intro x hx
    have hh := connected_block_no_joint_loop M hB hcB (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hzero : M.degIn (C ∩ Q) b1 = 0 := by
    rw [hinter]
    exact degIn_singleton_eq_zero M hno
  have hsum0 := outIn_add_inIn M (C ∩ Q) b1
  have ho0 : M.outIn (C ∩ Q) b1 = 0 := by omega
  have hi0 : M.inIn (C ∩ Q) b1 = 0 := by omega
  have hfull := hA.2.2.2.2.2.2.2.2.1 b1 hb1A hb11 hb12
  obtain ⟨hfullO,hfullI⟩ := full_oriented_counts M hM (hA.1 hb1A) hfull
  have hOut := outIn_union_add_inter M C Q hb1C hb1Q
  have hIn := inIn_union_add_inter M C Q hb1C hb1Q
  rw [hcover,ho0,hfullO] at hOut
  rw [hcover,hi0,hfullI] at hIn
  have hoQ := hQ.2.2.2.2.2.2.1
  have hiQ := hQ.2.2.2.2.2.2.2.1
  have hoC : M.outIn C b1 = 1 := by omega
  have hiC : M.inIn C b1 = 1 := by omega
  have hEq := left_piece_internal_eq M hM hB hb1A hb2out ha2P
  have ho2 : M.outIn C a2 = 1 :=
    (orientedIn_eq_of_internal_eq M hEq true).trans hA.2.2.2.2.2.2.1
  have hi2 : M.inIn C a2 = 1 :=
    (orientedIn_eq_of_internal_eq M hEq false).trans hA.2.2.2.2.2.2.2.1
  have hconnC : M.GroupConnected C := by
    classical
    have hcl : ∀ x ∈ A \ B, ∀ y ∈ A, M.Adj x y → y ∈ C := by
      intro x hx y hy hadj
      have hxB := (Finset.mem_sdiff.mp hx).2
      by_cases hyB : y ∈ B
      · rcases block_entry_is_joint M hM hB hxB hyB hadj with h | h
        · exact h ▸ hb1C
        · exact (hb2out (h ▸ hy)).elim
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy,hyB⟩)
    have hCne : ∀ x ∈ C, x ≠ b1 → x ∈ A \ B := by
      intro x hx hne
      rcases Finset.mem_union.mp hx with h | h
      · exact h
      · exact (hne (Finset.mem_singleton.mp h)).elim
    let E : Finset V → V → V → Prop := fun S a b =>
      ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b
    have hside : ∀ U : Finset V, (∀ x ∈ U, ∀ y ∈ A, M.Adj x y → y ∈ U) → ∀ u v,
        Relation.EqvGen (E A) u v → (u ∈ U ↔ v ∈ U) := by
      intro U hU u v hp
      induction hp with
      | rel a b hab =>
        obtain ⟨x, hx, rfl, rfl⟩ := hab
        exact ⟨fun h => hU _ h _ hx.2 ⟨x, rfl, rfl⟩,
          fun h => hU _ h _ hx.1 ⟨M.mate x, rfl, by rw [M.mate_mate]⟩⟩
      | refl a => exact Iff.rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
    have hall : ∀ x ∈ C, Relation.EqvGen (E C) b1 x := by
      intro x0 hx0
      by_contra hR
      let U := C.filter (fun x => ¬ Relation.EqvGen (E C) b1 x)
      have hx0U : x0 ∈ U := Finset.mem_filter.mpr ⟨hx0,hR⟩
      have hclU : ∀ x ∈ U, ∀ y ∈ A, M.Adj x y → y ∈ U := by
        intro x hx y hy hadj
        obtain ⟨hxC,hxR⟩ := Finset.mem_filter.mp hx
        have hxb : x ≠ b1 := by
          intro he; apply hxR; rw [he]; exact Relation.EqvGen.refl _
        have hyC := hcl x (hCne x hxC hxb) y hy hadj
        refine Finset.mem_filter.mpr ⟨hyC, fun hyR => hxR ?_⟩
        obtain ⟨d, hd1, hd2⟩ := hadj
        exact Relation.EqvGen.trans _ _ _ hyR (Relation.EqvGen.rel _ _
          ⟨M.mate d, ⟨hd2 ▸ hyC, by rw [M.mate_mate, hd1]; exact hxC⟩, hd2,
            by rw [M.mate_mate, hd1]⟩)
      have hpath := hA.2.2.2.2.2.2.2.2.2 x0 (hsub hx0) b1 (hsub hb1C)
      have hb1U : b1 ∈ U := (hside U hclU _ _ hpath).mp hx0U
      exact (Finset.mem_filter.mp hb1U).2 (Relation.EqvGen.refl _)
    refine fun u hu v hv => ?_
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall u hu)) (hall v hv)
  refine ⟨fun _ hz => hA.1 (hsub hz),ha2C,hb1C,Ne.symm hb12,ho2,hi2,hoC,hiC,?_,hconnC⟩
  intro z hz hza hzb
  have hzP : z ∈ A \ B := by
    rcases Finset.mem_union.mp hz with hzP | hzb1
    · exact hzP
    · exact (hzb (Finset.mem_singleton.mp hzb1)).elim
  have hzA := (Finset.mem_sdiff.mp hzP).1
  have hzB := (Finset.mem_sdiff.mp hzP).2
  have hza1 : z ≠ a1 := fun he => hzB (he.symm ▸ ha1B)
  have hd := hA.2.2.2.2.2.2.2.2.1 z hzA hza1 hza
  change ((M.dartsAt z).filter (M.InGroup C)).card = 4
  rw [left_piece_internal_eq M hM hB hb1A hb2out hzP]
  exact hd

end WaveTurbulence.Mole
