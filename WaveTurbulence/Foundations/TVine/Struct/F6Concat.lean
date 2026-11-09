/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.F6Chain
public import WaveTurbulence.Foundations.TVine.Struct.Families
import Mathlib.Tactic

/-!
# Concatenated members of a T-vine (packet L3; for N2 Thm 1.15 (F6), scenario (b))

**`concat_allowed`**: if two block members `U, W` of a T-vine meet exactly in `U.k₂ = W.k₁`, then `U ∪ W` (with
joints `U.k₁, W.k₂`; of hyper type iff these are joined by one bond) is a vine-like sub-object with kinds
`ks_U ++ ks_W`, so these kinds are allowed (N2 Thm 1.15 (F3), `subObj_single`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

/-- A bond at an inner atom of a sub-object stays inside it. -/
theorem mem_of_inner_bond {G : UMultigraph V} {j₁ j₂ : V} (hB : IsBlockU G j₁ j₂) {U : SubObj V}
    (hU : IsSubObjU G U) {x w : V} (hx : x ∈ U.atoms) (h1 : x ≠ U.k₁) (h2 : x ≠ U.k₂) (hw : w ∈ G.verts)
    (hm : G.mult s(x, w) ≠ 0) : w ∈ U.atoms := by
  by_contra hwA
  exact not_mem_inner_of_bond hB hU hw hwA (Nat.one_le_iff_ne_zero.mpr hm)
    (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hx⟩⟩)

theorem core_eq_induce {G : UMultigraph V} {U : SubObj V} (h : U.hyper = false) : U.core G = induce G U.atoms := by
  show (if U.hyper then eraseBond (SubObj.edges G U) s(U.k₁, U.k₂) else SubObj.edges G U) = _
  rw [h]; rfl

theorem joints_out {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U) :
    j₁ ∉ U.atoms ∧ j₂ ∉ U.atoms :=
  containerJoints_holds G j₁ j₂ U hT.1 (loopless_of_isTVineU hT)
    (interior_connOn (t6Ctx_of_isTVineU pendantPolesInput_holds hT)) (noCutVertex_holds G j₁ j₂ hT) hU

theorem deg_four {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂) {U : SubObj V} (hU : IsSubObjU G U)
    {v : V} (hv : v ∈ U.atoms) : deg G v = 4 :=
  hT.1.2.2.2.2.2.1 v (hU.1.subset hv) (fun h => (joints_out hT hU).1 (h ▸ hv))
    (fun h => (joints_out hT hU).2 (h ▸ hv))

theorem rtg_symm' {R : V → V → Prop} (hs : ∀ p q, R p q → R q p) {a b : V} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hs _ _ hbc) ih

theorem rtg_lift' {R R' : V → V → Prop} (hs : ∀ p q, R p q → R' p q) {a b : V} (h : Relation.ReflTransGen R a b) :
    Relation.ReflTransGen R' a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih (hs _ _ hbc)

/-- **Concatenated block members have allowed kinds.** -/
theorem concat_allowed (I : Thm115Inputs.{u}) {G : UMultigraph V} {j₁ j₂ : V} (hT : IsTVineU G j₁ j₂)
    {U W : SubObj V} {ksU ksW : List EnlKind} (hU : IsVineLikeU G U ksU) (hW : IsVineLikeU G W ksW)
    (hUb : U.hyper = false) (hWb : W.hyper = false) (hk : U.k₂ = W.k₁)
    (hP : U.atoms ∩ W.atoms = {W.k₁}) : AllowedKinds (ksU ++ ksW) := by
  classical
  have hB := hT.1
  have hl : G.Loopless := loopless_of_isTVineU hT
  have hAV : U.atoms ⊆ G.verts := hU.1.1.subset
  have hBV : W.atoms ⊆ G.verts := hW.1.1.subset
  have haA : U.k₁ ∈ U.atoms := k₁_mem hU.1
  have hkA : W.k₁ ∈ U.atoms := hk ▸ k₂_mem hU.1
  have hkB : W.k₁ ∈ W.atoms := k₁_mem hW.1
  have hcB : W.k₂ ∈ W.atoms := k₂_mem hW.1
  have hak : U.k₁ ≠ W.k₁ := hk ▸ hU.1.2.2.2.2.1
  have hck : W.k₂ ≠ W.k₁ := (hW.1.2.2.2.2.1).symm
  have haB : U.k₁ ∉ W.atoms := fun h =>
    hak (Finset.mem_singleton.mp (hP ▸ Finset.mem_inter.mpr ⟨haA, h⟩))
  have hcA : W.k₂ ∉ U.atoms := fun h =>
    hck (Finset.mem_singleton.mp (hP ▸ Finset.mem_inter.mpr ⟨h, hcB⟩))
  have hac : U.k₁ ≠ W.k₂ := fun h => haB (h ▸ hcB)
  set a := U.k₁
  set k := W.k₁
  set c := W.k₂
  set X := U.atoms ∪ W.atoms with hXdef
  set m := G.mult s(a, c) with hm
  have hXV : X ⊆ G.verts := Finset.union_subset hAV hBV
  -- degrees in the induced graphs
  have hdU : ∀ v ∈ U.atoms, ∑ w ∈ U.atoms, G.mult s(v, w) = if v = a ∨ v = k then 2 else 4 := by
    intro v hv
    rw [← deg_induce_eq G hl hv, ← core_eq_induce hUb]
    have hBU := hU.1.2.2
    split_ifs with h
    · rcases h with rfl | rfl
      · exact hBU.2.2.2.1
      · rw [show k = U.k₂ from hk.symm]; exact hBU.2.2.2.2.1
    · push_neg at h
      exact hBU.2.2.2.2.2.1 v (by rw [core_verts]; exact hv) h.1 (by rw [hk]; exact h.2)
  have hdW : ∀ v ∈ W.atoms, ∑ w ∈ W.atoms, G.mult s(v, w) = if v = k ∨ v = c then 2 else 4 := by
    intro v hv
    rw [← deg_induce_eq G hl hv, ← core_eq_induce hWb]
    have hBW := hW.1.2.2
    split_ifs with h
    · rcases h with rfl | rfl
      · exact hBW.2.2.2.1
      · exact hBW.2.2.2.2.1
    · push_neg at h
      exact hBW.2.2.2.2.2.1 v (by rw [core_verts]; exact hv) h.1 h.2
  have hsplit : ∀ v, ∑ w ∈ X, G.mult s(v, w) =
      ∑ w ∈ U.atoms, G.mult s(v, w) + ∑ w ∈ W.atoms, G.mult s(v, w) - G.mult s(v, k) := by
    intro v
    have := Finset.sum_union_inter (s₁ := U.atoms) (s₂ := W.atoms) (f := fun w => G.mult s(v, w))
    rw [hP, Finset.sum_singleton, ← hXdef] at this
    omega
  have hupper : ∀ v ∈ X, ∑ w ∈ X, G.mult s(v, w) ≤ 4 := by
    intro v hv
    have h1 := deg_induce G hv hXV
    rw [deg_induce_eq G hl hv] at h1
    have : deg G v = 4 := by
      rcases Finset.mem_union.mp hv with h | h
      · exact deg_four hT hU.1 h
      · exact deg_four hT hW.1 h
    omega
  -- the far joints see only each other on the other side
  have hsumWa : ∑ w ∈ W.atoms, G.mult s(a, w) = G.mult s(a, k) + m := by
    rw [← Finset.sum_pair (f := fun w => G.mult s(a, w)) (Ne.symm hck)]
    refine (Finset.sum_subset (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hkB
      · exact hcB) ?_).symm
    intro w hw hwn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwn
    by_contra hne
    have : a ∈ W.atoms := mem_of_inner_bond hB hW.1 hw hwn.1 hwn.2 (hAV haA) (by rw [Sym2.eq_swap]; exact hne)
    exact haB this
  have hsumUc : ∑ w ∈ U.atoms, G.mult s(c, w) = G.mult s(c, k) + m := by
    have hma : G.mult s(c, a) = m := by rw [hm, Sym2.eq_swap]
    rw [← hma, ← Finset.sum_pair (f := fun w => G.mult s(c, w)) (Ne.symm hak)]
    refine (Finset.sum_subset (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hkA
      · exact haA) ?_).symm
    intro w hw hwn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hwn
    by_contra hne
    have : c ∈ U.atoms := mem_of_inner_bond hB hU.1 hw hwn.2
      (by rw [show U.k₂ = k from hk]; exact hwn.1) (hBV hcB) (by rw [Sym2.eq_swap]; exact hne)
    exact hcA this
  have hdegX : ∀ v ∈ X, ∑ w ∈ X, G.mult s(v, w) = if v = a ∨ v = c then 2 + m else 4 := by
    intro v hv
    split_ifs with h
    · rcases h with rfl | rfl
      · rw [hsplit, hdU _ haA, if_pos (Or.inl rfl), hsumWa]; omega
      · rw [hsplit, hsumUc, hdW _ hcB, if_pos (Or.inr rfl)]; omega
    · push_neg at h
      by_cases hvk : v = k
      · rw [hvk, hsplit, hdU k hkA, if_pos (Or.inr rfl), hdW k hkB, if_pos (Or.inl rfl), hl k]
      · have hup := hupper v hv
        rcases Finset.mem_union.mp hv with hvA | hvB
        · have h4 := hdU v hvA
          rw [if_neg (by tauto)] at h4
          have : ∑ w ∈ U.atoms, G.mult s(v, w) ≤ ∑ w ∈ X, G.mult s(v, w) :=
            Finset.sum_le_sum_of_subset Finset.subset_union_left
          omega
        · have h4 := hdW v hvB
          rw [if_neg (by tauto)] at h4
          have : ∑ w ∈ W.atoms, G.mult s(v, w) ≤ ∑ w ∈ X, G.mult s(v, w) :=
            Finset.sum_le_sum_of_subset Finset.subset_union_right
          omega
  have hj₁X : j₁ ∉ X := fun h => by
    rcases Finset.mem_union.mp h with h | h
    · exact (joints_out hT hU.1).1 h
    · exact (joints_out hT hW.1).1 h
  have hdegG : ∀ v ∈ X, deg G v = 4 := fun v hv => by
    rcases Finset.mem_union.mp hv with h | h
    · exact deg_four hT hU.1 h
    · exact deg_four hT hW.1 h
  have hm2 : m ≤ 2 := by
    have := hupper a (Finset.mem_union_left _ haA)
    rw [hdegX a (Finset.mem_union_left _ haA), if_pos (Or.inl rfl)] at this; omega
  have hm2' : m ≠ 2 := by
    intro h2
    have hcut : cut G X = 0 := by
      unfold cut
      apply Finset.sum_eq_zero
      intro v hv
      have h1 := deg_induce G hv hXV
      rw [deg_induce_eq G hl hv, hdegX v hv, hdegG v hv] at h1
      split_ifs at h1 <;> omega
    have := two_le_cut (cutCtx_of_isTVineU hT) hXV (Finset.mem_union_left _ haA) hB.1 hj₁X
    omega
  set Xo : SubObj V := ⟨X, a, c, decide (m = 1)⟩ with hXo
  have hXatoms : Xo.atoms = X := rfl
  -- multiplicities of the core of `X` on each side
  have hmA : ∀ p ∈ U.atoms, ∀ q ∈ U.atoms, (Xo.core G).mult s(p, q) = (U.core G).mult s(p, q) := by
    intro p hp q hq
    rw [core_mult, core_mult, if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact Finset.mem_union_left _ hp
        · exact Finset.mem_union_left _ hq),
      if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact hp
        · exact hq), hUb]
    simp only [Bool.false_eq_true, false_and, if_false]
    rw [if_neg]
    rintro ⟨-, he⟩
    rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨rfl, -⟩
    · exact hcA hq
    · exact hcA hp
  have hmB : ∀ p ∈ W.atoms, ∀ q ∈ W.atoms, (Xo.core G).mult s(p, q) = (W.core G).mult s(p, q) := by
    intro p hp q hq
    rw [core_mult, core_mult, if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact Finset.mem_union_right _ hp
        · exact Finset.mem_union_right _ hq),
      if_pos (Finset.mem_sym2_iff.mpr fun z hz => by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact hp
        · exact hq), hWb]
    simp only [Bool.false_eq_true, false_and, if_false]
    rw [if_neg]
    rintro ⟨-, he⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact haB hp
    · exact haB hq
  -- degrees in the core of `X`
  have hcoreX : ∀ v ∈ X, deg (Xo.core G) v = if v = a ∨ v = c then 2 else 4 := by
    intro v hv
    by_cases h1 : m = 1
    · have hcore : Xo.core G = eraseBond (induce G X) s(a, c) := by
        show (if decide (m = 1) = true then eraseBond (SubObj.edges G Xo) s(a, c) else SubObj.edges G Xo) = _
        rw [if_pos (by simp [h1])]; rfl
      have hmi : (induce G X).mult s(a, c) ≠ 0 := by
        rw [Core.induce_mult_of_mem G (Finset.mem_union_left _ haA) (Finset.mem_union_right _ hcB)]; omega
      have := deg_eraseBond (induce G X) hac (Finset.mem_union_left _ haA) (Finset.mem_union_right _ hcB) hmi v
      rw [← hcore, deg_induce_eq G hl hv, hdegX v hv] at this
      split_ifs at this ⊢ <;> omega
    · have hcore : Xo.core G = induce G X := by
        show (if decide (m = 1) = true then eraseBond (SubObj.edges G Xo) s(a, c) else SubObj.edges G Xo) = _
        rw [if_neg (by simp [h1])]; rfl
      rw [hcore, deg_induce_eq G hl hv, hdegX v hv]
      split_ifs <;> omega
  -- connectivity of the core of `X`
  have hliftA : ∀ p q, AdjIn (U.core G) U.atoms p q → AdjIn (Xo.core G) X p q := fun p q h =>
    ⟨Finset.mem_union_left _ h.1, Finset.mem_union_left _ h.2.1, by rw [hmA p h.1 q h.2.1]; exact h.2.2⟩
  have hliftB : ∀ p q, AdjIn (W.core G) W.atoms p q → AdjIn (Xo.core G) X p q := fun p q h =>
    ⟨Finset.mem_union_right _ h.1, Finset.mem_union_right _ h.2.1, by rw [hmB p h.1 q h.2.1]; exact h.2.2⟩
  have hconnU : ConnOn (U.core G) U.atoms := by
    have := hU.1.2.2.2.2.2.2.2.2; unfold Connected at this; rwa [core_verts] at this
  have hconnW : ConnOn (W.core G) W.atoms := by
    have := hW.1.2.2.2.2.2.2.2.2; unfold Connected at this; rwa [core_verts] at this
  have htok : ∀ x ∈ X, Relation.ReflTransGen (AdjIn (Xo.core G) X) x k := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact rtg_lift' hliftA (hconnU x h k hkA)
    · exact rtg_lift' hliftB (hconnW x h k hkB)
  have hsym : ∀ p q, AdjIn (Xo.core G) X p q → AdjIn (Xo.core G) X q p := fun p q h =>
    ⟨h.2.1, h.1, by rw [Sym2.eq_swap]; exact h.2.2⟩
  have hconnX : ConnOn (Xo.core G) X := by
    intro x hx y hy
    exact (htok x hx).trans (rtg_symm' hsym (htok y hy))
  have hXsub : IsSubObjU G Xo := by
    refine ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hXV, fun h => hj₁X (by show j₁ ∈ Xo.atoms; rw [h]; exact hB.1)⟩, fun hh => ?_, ?_⟩
    · have hh' : decide (m = 1) = true := hh
      have : m = 1 := by simpa using hh'
      show G.mult s(a, c) ≠ 0; omega
    · refine ⟨by rw [core_verts]; exact Finset.mem_union_left _ haA,
        by rw [core_verts]; exact Finset.mem_union_right _ hcB, hac, ?_, ?_, ?_, ?_⟩
      · have := hcoreX a (Finset.mem_union_left _ haA); rwa [if_pos (Or.inl rfl)] at this
      · have := hcoreX c (Finset.mem_union_right _ hcB); rwa [if_pos (Or.inr rfl)] at this
      · intro v hv h1 h2
        rw [core_verts] at hv
        have := hcoreX v hv; rwa [if_neg (by tauto)] at this
      · unfold Connected; rw [core_verts]; exact hconnX
  have hUc : ChainU (U.core G) U.atoms a k ksU := hk ▸ hU.2
  have hchain : ChainU (Xo.core G) X a c (ksU ++ ksW) :=
    ChainU.concat' (ChainU.congr hUc hmA) (ChainU.congr hW.2 hmB) hP hac
  exact (subObj_single I _ G j₁ j₂ rfl hT Xo (ksU ++ ksW) ⟨hXsub, hchain⟩).1

end WaveTurbulence.TVine.Struct
