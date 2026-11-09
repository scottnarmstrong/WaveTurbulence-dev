/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Thm6Pend
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F1): `disjointlem` (i) and (ii) for T-vines (packet L3)

For a T6 context (cut context, joint degrees 2, interior degrees 4, N3 Lemma 6.2):

* `interior_connOn` ((F1)(i), DH23 `disjointlem` (i)): the interior `S ∖ {j₁, j₂}` is connected. If it split into
  `A ⊔ B` with no bond between, the joints (which carry `4 − 2σ ≤ 4` bonds) would give `cut A = cut B = 2`: two disjoint
  joint-free 2-poles, against Lemma 6.2. (No rung induction and no finite base are needed.)
* `erase_connOn` ((F1)(ii), no interior cut atom; N3 Lemma 4.1): if `S ∖ {v}` split into `A ⊔ B`, both sides would be
  attached to `v` by exactly two bonds, so `v` would carry both bonds of a 2-edge-cut, against Lemma A (which needs
  the piece shape: pieces have at least two atoms).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core CutAlg

variable {V : Type*} [DecidableEq V] {G : UMultigraph V} {j₁ j₂ : V}

/-- The weight from a set of interior atoms to the joints is at most `4`. -/
theorem eW_joints_le (hT : T6Ctx G j₁ j₂) {A : Finset V} (hA : A ⊆ G.verts) :
    eW (wG G) A {j₁, j₂} ≤ 4 := by
  have hw := symm_wG G
  rw [eW_comm hw, Finset.insert_eq, eW_union_left _ (Finset.disjoint_singleton.mpr hT.ne)]
  have h1 : eW (wG G) {j₁} A ≤ deg G j₁ := by
    rw [← degW_eq_deg hT.cc.loopless]
    unfold eW degW; rw [Finset.sum_singleton]
    exact Finset.sum_le_sum_of_subset hA
  have h2 : eW (wG G) {j₂} A ≤ deg G j₂ := by
    rw [← degW_eq_deg hT.cc.loopless]
    unfold eW degW; rw [Finset.sum_singleton]
    exact Finset.sum_le_sum_of_subset hA
  rw [hT.deg₁] at h1; rw [hT.deg₂] at h2
  omega

/-- **(F1)(i)**: the interior of a T-vine is connected. -/
theorem interior_connOn (hT : T6Ctx G j₁ j₂) : ConnOn G (Core.interior G j₁ j₂) := by
  classical
  have hw := symm_wG G
  intro u hu w hw'
  by_contra hnot
  set I := Core.interior G j₁ j₂ with hIdef
  have hIV : I ⊆ G.verts := interior_subset_verts j₁ j₂
  set A := reach (wG G) I u with hAdef
  have hAI : A ⊆ I := fun x hx => (mem_reach.mp hx).1
  have huA : u ∈ A := mem_reach.mpr ⟨hu, Relation.ReflTransGen.refl⟩
  have hwA : w ∉ A := fun h => hnot (mem_reach.mp h).2
  set B := I \ A with hBdef
  have hwB : w ∈ B := Finset.mem_sdiff.mpr ⟨hw', hwA⟩
  have hAB : eW (wG G) A B = 0 := eW_reach_zero u
  have hdAB : Disjoint A B := Finset.disjoint_sdiff
  have hJ : Disjoint I {j₁, j₂} := by
    rw [Finset.disjoint_left]; intro x hx hxJ
    rw [mem_interior] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxJ
    rcases hxJ with rfl | rfl
    · exact hx.2.1 rfl
    · exact hx.2.2 rfl
  -- the complement of `A` is `B` plus the joints
  have hcomp : ∀ {C D : Finset V}, C ∪ D = I → Disjoint C D → G.verts \ C = D ∪ {j₁, j₂} := by
    intro C D hCD hd
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxC⟩
      by_cases h1 : x = j₁
      · exact Or.inr (Or.inl h1)
      by_cases h2 : x = j₂
      · exact Or.inr (Or.inr h2)
      have : x ∈ I := mem_interior.mpr ⟨hx, h1, h2⟩
      rw [← hCD] at this
      exact Or.inl ((Finset.mem_union.mp this).resolve_left hxC)
    · rintro (hx | rfl | rfl)
      · have hxI : x ∈ I := by rw [← hCD]; exact Finset.mem_union_right _ hx
        exact ⟨hIV hxI, fun hxC => Finset.disjoint_left.mp hd hxC hx⟩
      · exact ⟨hT.mem₁, fun h => Finset.disjoint_left.mp hJ (hCD ▸ Finset.mem_union_left _ h) (by simp)⟩
      · exact ⟨hT.mem₂, fun h => Finset.disjoint_left.mp hJ (hCD ▸ Finset.mem_union_left _ h) (by simp)⟩
  have hUAB : A ∪ B = I := Finset.union_sdiff_of_subset hAI
  have hcutA : cut G A = eW (wG G) A {j₁, j₂} := by
    rw [cut_eq_eW, hcomp hUAB hdAB, eW_union_right _ (hJ.mono_left Finset.sdiff_subset), hAB, zero_add]
  have hcutB : cut G B = eW (wG G) B {j₁, j₂} := by
    rw [cut_eq_eW, hcomp (by rw [Finset.union_comm]; exact hUAB) hdAB.symm,
      eW_union_right _ (hJ.mono_left hAI), eW_comm hw B A, hAB, zero_add]
  have hsum : eW (wG G) A {j₁, j₂} + eW (wG G) B {j₁, j₂} ≤ 4 := by
    rw [← eW_union_left _ hdAB, hUAB]; exact eW_joints_le hT hIV
  have hA2 : 2 ≤ cut G A := two_le_cut hT.cc (hAI.trans hIV) huA hT.mem₁ (fun h => (mem_interior.mp (hAI h)).2.1 rfl)
  have hB2 : 2 ≤ cut G B := two_le_cut hT.cc (Finset.sdiff_subset.trans hIV) hwB hT.mem₁
    (fun h => (mem_interior.mp (Finset.sdiff_subset h)).2.1 rfl)
  exact hT.noPend A B hAI Finset.sdiff_subset hdAB ⟨u, huA⟩ ⟨w, hwB⟩ (by omega) (by omega)

/-- **(F1)(ii)**: a T-vine with the piece shape has no interior cut atom. -/
theorem erase_connOn (hT : T6Ctx G j₁ j₂) (hbig : ∀ P ∈ piecesU G j₁ j₂, 2 ≤ P.card) {v : V}
    (hv : v ∈ Core.interior G j₁ j₂) : ConnOn G (G.verts.erase v) := by
  classical
  have hw := symm_wG G
  have hvV : v ∈ G.verts := interior_subset_verts j₁ j₂ hv
  intro u hu w hw'
  by_contra hnot
  set R := G.verts.erase v with hRdef
  have hRV : R ⊆ G.verts := Finset.erase_subset _ _
  set A := reach (wG G) R u with hAdef
  have hAR : A ⊆ R := fun x hx => (mem_reach.mp hx).1
  have huA : u ∈ A := mem_reach.mpr ⟨hu, Relation.ReflTransGen.refl⟩
  have hwA : w ∉ A := fun h => hnot (mem_reach.mp h).2
  set B := R \ A with hBdef
  have hwB : w ∈ B := Finset.mem_sdiff.mpr ⟨hw', hwA⟩
  have hAB : eW (wG G) A B = 0 := eW_reach_zero u
  have hdAB : Disjoint A B := Finset.disjoint_sdiff
  have hvA : v ∉ A := fun h => (Finset.mem_erase.mp (hAR h)).1 rfl
  have hvB : v ∉ B := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
  have hUAB : A ∪ B = R := Finset.union_sdiff_of_subset hAR
  have hcomp : G.verts \ A = B ∪ {v} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxV, hxA⟩ := Finset.mem_sdiff.mp hx
      by_cases hxv : x = v
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hxv)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxV⟩, hxA⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨hRV h1, h2⟩
      · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_sdiff.mpr ⟨hvV, hvA⟩
  have hcutA : cut G A = eW (wG G) A {v} := by
    rw [cut_eq_eW, hcomp, eW_union_right _ (Finset.disjoint_singleton_right.mpr hvB), hAB, zero_add]
  have hA2 : 2 ≤ cut G A := two_le_cut hT.cc (hAR.trans hRV) huA hvV hvA
  have hdeg := deg_split (G := G) hT.cc (X := insert v A) (Finset.insert_subset hvV (hAR.trans hRV))
    (Finset.mem_insert_self v A)
  rw [Finset.erase_insert hvA] at hdeg
  -- the cut of `A` consists of bonds at `v`
  have hle := attachU_compl hT.cc (fun x hx => by rw [mem_interior] at hx; exact hT.deg4 x hx.1 hx.2.1 hx.2.2) hbig
    (hAR.trans hRV) (by
      have hev := cut_even hT.cc (hAR.trans hRV)
      have h4 : eW (wG G) A {v} ≤ 2 := by
        -- the other side `B` also has cut at least 2, and both cuts are bonds at `v` (degree 4)
        have hcomp' : G.verts \ B = A ∪ {v} := by
          ext x
          constructor
          · intro hx
            obtain ⟨hxV, hxB⟩ := Finset.mem_sdiff.mp hx
            by_cases hxv : x = v
            · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hxv)
            · refine Finset.mem_union_left _ ?_
              by_contra hxA; exact hxB (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, hxV⟩, hxA⟩)
          · intro hx
            rcases Finset.mem_union.mp hx with hx | hx
            · exact Finset.mem_sdiff.mpr ⟨hRV (hAR hx), fun h => Finset.disjoint_left.mp hdAB hx h⟩
            · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_sdiff.mpr ⟨hvV, hvB⟩
        have hcutB : cut G B = eW (wG G) B {v} := by
          rw [cut_eq_eW, hcomp', eW_union_right _ (Finset.disjoint_singleton_right.mpr hvA), eW_comm hw B A, hAB,
            zero_add]
        have hB2 : 2 ≤ cut G B := two_le_cut hT.cc (Finset.sdiff_subset.trans hRV) hwB hvV hvB
        have hsplit : eW (wG G) A {v} + eW (wG G) B {v} = deg G v := by
          rw [← eW_union_left _ hdAB, hUAB, eW_comm hw, ← degW_eq_deg hT.cc.loopless]
          unfold eW degW; rw [Finset.sum_singleton, ← Finset.sum_erase_add G.verts _ hvV]
          have := hT.cc.loopless v; simp only [wG] at this ⊢; rw [this, add_zero]
        rw [mem_interior] at hv
        rw [hT.deg4 v hvV hv.2.1 hv.2.2] at hsplit
        omega
      obtain ⟨k, hk⟩ := hev
      omega) hv hvA
  rw [eW_comm hw] at hle
  omega

end WaveTurbulence.TVine.Struct
