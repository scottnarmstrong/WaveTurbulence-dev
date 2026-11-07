/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.FinalCount.S1Erase
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
import Mathlib.Tactic

/-!
# Ingredients of a maximal group: separation, for both the VC and the HVC alternatives

`ing_pair`: two distinct ingredients (`IsIngredient`) of the same group meet in at most one atom, and
the common atom has internal degree `2` in both.  The two certificates may use different deleted
bonds; the entries of an HVC chain never contain both joints, so they are vines of `M` itself.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace ChainL
variable {N : Molecule V D} {U : Finset V} {a b : V} {L : List (Finset V × V × V)}

theorem joints (h : ChainL N U a b L) : a ≠ b ∧ a ∈ U ∧ b ∈ U := by
  induction h with
  | single hv => obtain ⟨X, hX⟩ := hv; exact ⟨hX.1.2.2.2.1, hX.1.2.1, hX.1.2.2.1⟩
  | append _ hT _ hne ih =>
    obtain ⟨X, hX⟩ := hT
    exact ⟨hne, mem_union_left _ ih.2.1, mem_union_right _ hX.1.2.2.1⟩

/-- In a chain with at least two ingredients no ingredient contains both end joints. -/
theorem entry_not_both (h : ChainL N U a b L) (hl : 2 ≤ L.length) :
    ∀ t ∈ L, ¬ (a ∈ t.1 ∧ b ∈ t.1) := by
  induction h with
  | single _ => simp at hl
  | @append S T a b c L hL hT hi hne _ =>
    obtain ⟨X, hX⟩ := hT
    intro t ht ⟨ha, hc⟩
    rcases List.mem_append.mp ht with ht | ht
    · have hcS : c ∈ S := hL.entry_subset t ht hc
      have : c ∈ S ∩ T := mem_inter.mpr ⟨hcS, hX.1.2.2.1⟩
      rw [hi] at this
      have hcb : c = b := by simpa using this
      exact hX.1.2.2.2.1 hcb.symm
    · simp only [List.mem_singleton] at ht
      subst ht
      have hat : a ∈ S ∩ T := mem_inter.mpr ⟨hL.joints.2.1, ha⟩
      rw [hi] at hat
      have hab : a = b := by simpa using hat
      exact hL.joints.1 hab

/-- Transport of a decomposition to another molecule in which every entry is still a vine. -/
theorem map {D' : Type*} [Fintype D'] [DecidableEq D'] {N' : Molecule V D'} (h : ChainL N U a b L)
    (hv : ∀ t ∈ L, Vine.IsSomeVine N t.1 t.2.1 t.2.2 → Vine.IsSomeVine N' t.1 t.2.1 t.2.2) :
    ChainL N' U a b L := by
  induction h with
  | single h0 => exact ChainL.single (hv (_, _, _) (by simp) h0)
  | append hL hT hi hne ih =>
    refine ChainL.append (ih fun t ht => hv t (List.mem_append_left _ ht)) ?_ hi hne
    exact hv (_, _, _) (by simp) hT

end ChainL

section Erase
variable {M : Molecule V D}

theorem degIn_eraseBond_of_not_inGroup (e : D) {S : Finset V} (he : ¬ M.InGroup S e) (v : V) :
    (Molecule.eraseBond M e).degIn S v = M.degIn S v := by
  have h1 : (Molecule.eraseBond M e).degIn S v =
      (((M.dartsAt v).filter (M.InGroup S)) \ {e, M.mate e}).card :=
    Mole.eraseBond_degIn M e S v
  rw [h1]
  unfold Molecule.degIn
  congr 1
  apply Finset.sdiff_eq_self_iff_disjoint.mpr
  rw [Finset.disjoint_right]
  intro x hx hxv
  have hxg := (Finset.mem_filter.mp hxv).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact he hxg
  · exact he (by simpa only [M.mate_mate] using inGroup_mate' hxg)

theorem isBlock_of_eraseBond {S : Finset V} {a b : V} (e : D)
    (hB : (Molecule.eraseBond M e).IsBlock S a b) (he : ¬ M.InGroup S e) : M.IsBlock S a b := by
  obtain ⟨hS, ha, hb, hne, ho1, hi1, ho2, hi2, hint, hconn⟩ := hB
  have hori : ∀ v (c : Bool), (((Molecule.eraseBond M e).dartsAt v).filter
      (fun x => (Molecule.eraseBond M e).InGroup S x ∧ (Molecule.eraseBond M e).out x = c)).card =
      ((M.dartsAt v).filter (fun x => M.InGroup S x ∧ M.out x = c)).card :=
    fun v c => Mole.eraseBond_orientedIn M e S v c he
  refine ⟨hS, ha, hb, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hori a true).symm.trans ho1
  · exact (hori a false).symm.trans (by
      have := hi1
      unfold Molecule.inIn at this
      simpa using this)
  · exact (hori b true).symm.trans ho2
  · exact (hori b false).symm.trans (by
      have := hi2
      unfold Molecule.inIn at this
      simpa using this)
  · intro v hv h1 h2
    exact (degIn_eraseBond_of_not_inGroup e he v).symm.trans (hint v hv h1 h2)
  · intro u hu v hv
    refine Relation.EqvGen.mono ?_ u v (hconn u hu v hv)
    rintro p q ⟨x, hx, hxp, hxq⟩
    exact ⟨x.1, hx, hxp, hxq⟩

theorem isVine_of_eraseBond {X : VineType} {S : Finset V} {a b : V} (e : D)
    (hV : (Molecule.eraseBond M e).IsVine X S a b) (he : ¬ M.InGroup S e) : M.IsVine X S a b := by
  obtain ⟨hB, k, hk, f, hf, hi, hj, hg⟩ := hV
  exact ⟨isBlock_of_eraseBond e hB he, k, hk, f, hf, hi, hj, by rw [← eraseBond_groupBonds_eq e he]; exact hg⟩

end Erase

theorem inGroup_iff_ends {M : Molecule V D} {e : D} {a b : V} (he : M.ends e = s(a, b))
    (t : Finset V) : M.InGroup t e ↔ a ∈ t ∧ b ∈ t := by
  have hend := Sym2.eq_iff.mp he
  change (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) at hend
  unfold Molecule.InGroup
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, and_comm]

theorem isBlock_symm {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsBlock S a b) :
    M.IsBlock S b a := by
  obtain ⟨hS, ha, hb, hne, ho1, hi1, ho2, hi2, hint, hconn⟩ := h
  exact ⟨hS, hb, ha, hne.symm, ho2, hi2, ho1, hi1,
    fun v hv h1 h2 => hint v hv h2 h1, hconn⟩

/-- The data extracted from an HVC-type ingredient certificate. -/
theorem hvc_data {M : Molecule V D} {S T : Finset V} {a b : V} {e : D} {n : ℕ} {x y : V}
    (he : M.ends e = s(a, b)) (hn : 2 ≤ n) (_hB : (Molecule.eraseBond M e).IsBlock S a b)
    (hc : Vine.ChainIngredient (Molecule.eraseBond M e) S a b n T x y) :
    ∃ L, ChainL (Molecule.eraseBond M e) S a b L ∧ (T, x, y) ∈ L ∧
      (∀ t ∈ L, ¬ M.InGroup t.1 e) := by
  obtain ⟨L, hL, hm, hl⟩ := exists_chainL_of_ingredient hc
  refine ⟨L, hL, hm, fun t ht hg => ?_⟩
  obtain ⟨h1, h2⟩ := (inGroup_iff_ends he t.1).mp hg
  exact hL.entry_not_both (by omega) t ht ⟨h1, h2⟩

/-- Two distinct ingredients of one group meet in at most one atom, which has internal degree `2` in
both (both certificates may be of VC type or of HVC type, with possibly different deleted bonds). -/
theorem ing_pair {M : Molecule V D} (hM : M.IsMolecule) {S T T' : Finset V}
    (h : IsIngredient M S T) (h' : IsIngredient M S T') (hne : T ≠ T') :
    (∀ z ∈ T ∩ T', ∀ z' ∈ T ∩ T', z = z') ∧
      (∀ z ∈ T ∩ T', M.degIn T z = 2 ∧ M.degIn T' z = 2) := by
  rcases h with ⟨a1, b1, n1, x1, y1, hB1, hc1⟩ | ⟨a1, b1, e1, n1, x1, y1, he1, hn1, hB1, hc1⟩ <;>
  rcases h' with ⟨a2, b2, n2, x2, y2, hB2, hc2⟩ | ⟨a2, b2, e2, n2, x2, y2, he2, hn2, hB2, hc2⟩
  · exact ingredientIn_sep hM ⟨a1, b1, n1, x1, y1, hB1, hc1⟩ ⟨a2, b2, n2, x2, y2, hB2, hc2⟩ hne
  · exact (not_block_and_hyper hB1 he2 hB2).elim
  · exact (not_block_and_hyper hB2 he1 hB1).elim
  · -- both HVC
    obtain ⟨L1, hL1, hm1, hf1⟩ := hvc_data he1 hn1 hB1 hc1
    obtain ⟨L2, hL2, hm2, hf2⟩ := hvc_data he2 hn2 hB2 hc2
    have hd1 := Mole.hyperBlock_degrees M (j1 := a1) (j2 := b1) ⟨e1, he1, hB1⟩
    have hd2 := Mole.hyperBlock_degrees M (j1 := a2) (j2 := b2) ⟨e2, he2, hB2⟩
    have ha2 : a2 = a1 ∨ a2 = b1 := by
      by_contra hc
      have := hd1.2.2 a2 (hB2.2.1) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      omega
    have hb2 : b2 = a1 ∨ b2 = b1 := by
      by_contra hc
      have := hd1.2.2 b2 (hB2.2.2.1) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      omega
    have hab2 := hB2.2.2.2.1
    -- the joints of the two certificates coincide as ordered or swapped pairs
    have hends : M.ends e2 = s(a1, b1) := by
      rw [he2]
      rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
      · exact absurd rfl hab2
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hab2
    have hB2' : (Molecule.eraseBond M e2).IsBlock S a1 b1 := by
      rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
      · exact absurd rfl hab2
      · exact hB2
      · exact isBlock_symm hB2
      · exact absurd rfl hab2
    have hmol1 : Molecule.eraseBond M e1 |>.IsMolecule := by
      have : M.atom e1 ≠ M.atom (M.mate e1) := by
        have hend := Sym2.eq_iff.mp he1
        change (M.atom e1 = a1 ∧ M.atom (M.mate e1) = b1) ∨ (M.atom e1 = b1 ∧ M.atom (M.mate e1) = a1) at hend
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> [exact hB1.2.2.2.1; exact hB1.2.2.2.1.symm]
      exact Vine.eraseBond_isMolecule M hM e1 this
    -- lift the first decomposition to the second erased molecule
    have hL1' : ChainL (Molecule.eraseBond M e2) S a1 b1 L1 := by
      refine hL1.map fun t ht hv => ?_
      obtain ⟨X, hX⟩ := hv
      have hfree1 := hf1 t ht
      have hfree2 : ¬ M.InGroup t.1 e2 := by
        rw [inGroup_iff_ends hends]
        rw [inGroup_iff_ends he1] at hfree1
        exact hfree1
      exact ⟨X, isVine_eraseBond e2 (isVine_of_eraseBond e1 hX hfree1) hfree2⟩
    have hmol2 : (Molecule.eraseBond M e2).IsMolecule := by
      have : M.atom e2 ≠ M.atom (M.mate e2) := by
        have hend := Sym2.eq_iff.mp hends
        change (M.atom e2 = a1 ∧ M.atom (M.mate e2) = b1) ∨ (M.atom e2 = b1 ∧ M.atom (M.mate e2) = a1) at hend
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact hB2'.2.2.2.1
        · exact hB2'.2.2.2.1.symm
      exact Vine.eraseBond_isMolecule M hM e2 this
    have hBS : (Molecule.eraseBond M e2).IsBlock S a1 b1 := hB2'
    obtain ⟨hs1, hs2⟩ := chainL_sep hmol2 hL1' hBS hL2 hB2 hm1 hm2 hne
    have hfT : ¬ M.InGroup T e2 := by
      rw [inGroup_iff_ends hends]
      have := hf1 _ hm1
      rw [inGroup_iff_ends he1] at this
      exact this
    have hfT' : ¬ M.InGroup T' e2 := hf2 _ hm2
    refine ⟨hs1, fun z hz => ?_⟩
    have := hs2 z hz
    rw [degIn_eraseBond_of_not_inGroup e2 hfT, degIn_eraseBond_of_not_inGroup e2 hfT'] at this
    exact this
  
end WaveTurbulence.Stage1
