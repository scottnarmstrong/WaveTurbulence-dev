/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.ObjBridge2
import Mathlib.Tactic

/-!
# Allowed kinds give L6's member types (packet L3)

* `ingredient_I`: an (I) ingredient is a double bond on two atoms;
* **`memberType_of_kinds`**: a vine-like `Src.Object` inside a T-vine whose L1 sub-object has allowed kinds
  (`[I]`, `[I, I]`, `[T]`) has L6's `TVineMemberType` (a hyper (I) would need a triple bond).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core GammaLow.FinalCount

universe u v

/-- An (I) ingredient is a double bond on two atoms. -/
theorem ingredient_I {V : Type*} [DecidableEq V] {H : UMultigraph V} {a c : V} (h : IsVineXU .I H a c)
    (hl : ∀ v, H.mult s(v, v) = 0) : H.verts = {a, c} ∧ H.mult s(a, c) = 2 := by
  have hB := h.1
  have hcard := card_isVineXU_I h
  have hsub : ({a, c} : Finset V) ⊆ H.verts := Finset.insert_subset hB.1 (Finset.singleton_subset_iff.mpr hB.2.1)
  have hv : H.verts = {a, c} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hB.2.2.1])).symm
  refine ⟨hv, ?_⟩
  have hd := hB.2.2.2.1
  unfold deg at hd
  rw [hv, Finset.sum_pair hB.2.2.1, hl a] at hd
  omega

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem loopless_groupGraph_sub {M : Molecule V D} {S A : Finset V} (hAS : A ⊆ S)
    (hl : ∀ v, (groupGraph M S).mult s(v, v) = 0) (v : V) : (groupGraph M A).mult s(v, v) = 0 := by
  rw [← groupGraph_induce M hAS]
  show (if s(v, v) ∈ A.sym2 then _ else 0) = 0
  split_ifs
  · exact hl v
  · rfl

/-- The VC:I+I clause from two (I) ingredients. -/
theorem isVCII_of_chain {V' D' : Type*} [DecidableEq V'] [Fintype D'] [DecidableEq D'] {M : Molecule V' D'}
    {A : Finset V'} {a b : V'} (h : ChainU (groupGraph M A) A a b [.I, .I])
    (hl : ∀ v, (groupGraph M A).mult s(v, v) = 0) : IsVCII M A a b := by
  obtain ⟨S', T, c, h1, hk, hST, hab, hA⟩ := chain_append_inv (ks := [.I]) (List.cons_ne_nil _ _) h
  have hk1 := chain_single_inv h1
  obtain ⟨hS'A, -⟩ : S' ⊆ A ∧ T ⊆ A := ⟨hA ▸ Finset.subset_union_left, hA ▸ Finset.subset_union_right⟩
  have hTA : T ⊆ A := hA ▸ Finset.subset_union_right
  rw [groupGraph_induce M hS'A] at hk1
  rw [groupGraph_induce M hTA] at hk
  obtain ⟨hv1, hm1⟩ := ingredient_I hk1 (loopless_groupGraph_sub hS'A hl)
  obtain ⟨hv2, hm2⟩ := ingredient_I hk (loopless_groupGraph_sub hTA hl)
  have hB1 := hk1.1
  have hB2 := hk.1
  refine ⟨c, Ne.symm hB1.2.2.1, hB2.2.2.1, hab, ?_, ?_, ?_⟩
  · rw [hA, show S' = {a, c} from hv1, show T = {c, b} from hv2]
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [bondsBetween_eq M (show a ∈ S' from hB1.1) (show c ∈ S' from hB1.2.1)]; exact hm1
  · rw [bondsBetween_eq M (show c ∈ T from hB2.1) (show b ∈ T from hB2.2.1)]; exact hm2

/-- **Allowed kinds give L6's member types** inside a T-vine. -/
theorem memberType_of_kinds {γ : ℝ} {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hT : M.IsTVine S j₁ j₂)
    (U : Src.Object γ M) (hUS : U.atoms ⊂ S) {ks : List EnlKind}
    (hU : IsVineLikeU (groupGraph M S) (suOf U) ks) (hk : AllowedKinds ks) : TVineMemberType M U := by
  have hlS : ∀ v, (groupGraph M S).mult s(v, v) = 0 := loopless_of_isTVineU ((isTVine_iff M).mp hT).2
  obtain ⟨A, a, b, sh⟩ := U
  have hAS : A ⊆ S := hUS.subset
  have hlA := loopless_groupGraph_sub hAS hlS
  cases sh with
  | vc h =>
    show M.IsVine .I A a b ∨ IsVCII M A a b ∨ M.IsTVine A a b
    have hch : ChainU (groupGraph M A) A a b ks := by
      have := hU.2; rw [core_suOf_vc h hAS] at this; exact this
    rcases hk with rfl | rfl | rfl
    · left
      have hX := chain_single_inv hch
      rw [groupGraph_induce M (subset_refl A)] at hX
      exact (isVine_iff M .I).mpr ⟨h.1, hX⟩
    · right; left
      exact isVCII_of_chain hch hlA
    · right; right
      have hX := chain_single_inv hch
      rw [groupGraph_induce M (subset_refl A)] at hX
      exact (isTVine_iff M).mpr ⟨h.1, hX⟩
  | hyper R =>
    show IsVCII (M.eraseBond R.added) A a b ∨ (M.eraseBond R.added).IsTVine A a b
    have hch : ChainU (groupGraph (M.eraseBond R.added) A) A a b ks := by
      have := hU.2; rw [core_suOf_hyper R hAS] at this; exact this
    have hlE : ∀ v, (groupGraph (M.eraseBond R.added) A).mult s(v, v) = 0 := by
      intro v
      have hB := R.adjoint.1
      have he : M.InGroup A R.added := by
        have := R.ends_eq
        simp only [Molecule.ends, Sym2.eq_iff] at this
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by rw [h1]; exact hB.2.1, by rw [h2]; exact hB.2.2.1⟩
        · exact ⟨by rw [h1]; exact hB.2.2.1, by rw [h2]; exact hB.2.1⟩
      rw [groupGraph_eraseBond M he]
      show (if s(v, v) = M.ends R.added then _ - 1 else _) = 0
      split_ifs <;> simp [hlA v]
    rcases hk with rfl | rfl | rfl
    · exfalso
      have hX := chain_single_inv hch
      rw [groupGraph_induce _ (subset_refl A)] at hX
      obtain ⟨-, hm⟩ := ingredient_I hX hlE
      have hB := R.adjoint.1
      have he : M.InGroup A R.added := by
        have := R.ends_eq
        simp only [Molecule.ends, Sym2.eq_iff] at this
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by rw [h1]; exact hB.2.1, by rw [h2]; exact hB.2.2.1⟩
        · exact ⟨by rw [h1]; exact hB.2.2.1, by rw [h2]; exact hB.2.1⟩
      rw [groupGraph_eraseBond M he] at hm
      have hm' : (if s(a, b) = M.ends R.added then (groupGraph M A).mult s(a, b) - 1
          else (groupGraph M A).mult s(a, b)) = 2 := hm
      rw [if_pos R.ends_eq.symm] at hm'
      have h3 : M.bondsBetween a b = 3 := by
        rw [bondsBetween_eq M (show a ∈ A from hB.2.1) (show b ∈ A from hB.2.2.1)]
        have := groupGraph_mult_ne_zero_of_dart M he
        rw [R.ends_eq] at this
        omega
      have := hT.2.1 a (hAS hB.2.1) b (hAS hB.2.2.1) hB.2.2.2.1
      omega
    · left
      exact isVCII_of_chain hch hlE
    · right
      have hX := chain_single_inv hch
      rw [groupGraph_induce _ (subset_refl A)] at hX
      exact (isTVine_iff _).mpr ⟨R.adjoint.1, hX⟩

end WaveTurbulence.TVine.Struct
