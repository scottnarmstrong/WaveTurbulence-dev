/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.SubObjU2
import Mathlib.Tactic

/-!
# Removing a disjoint family of sub-objects: the closed formula (packet L3)

L1's `removeAll G Us` removes the members one after the other (sources' semantics). For a pairwise atom-disjoint
family inside `G` it has the closed form

`verts = G.verts ∖ ⋃ I(U)`, `mult e = G.mult e − Σ_U (U° in G).mult e` (on the remaining atoms),

so it does not depend on the order (`removeAll_eq`). Consequences: `connected_removeAll_of_removeAllN` (N2's stronger
semantics removes more) and `mult_removeAll_of_out`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem mem_innerAll {Us : List (SubObj V)} {x : V} : x ∈ Checker.innerAll Us ↔ ∃ U ∈ Us, x ∈ U.inner := by
  induction Us with
  | nil => simp [Checker.innerAll]
  | cons U Us ih =>
    show x ∈ U.inner ∪ Checker.innerAll Us ↔ _
    rw [Finset.mem_union, ih]
    simp

theorem mem_sym2_of_mult_ne_zero (G : UMultigraph V) {e : Sym2 V} (h : G.mult e ≠ 0) : e ∈ G.verts.sym2 :=
  Finset.mem_sym2_iff.mpr fun x hx => G.supp e h x hx

/-- **The multiplicity of the core.** -/
theorem core_mult (H : UMultigraph V) (W : SubObj V) (e : Sym2 V) :
    (W.core H).mult e = if e ∈ W.atoms.sym2 then
      (if W.hyper = true ∧ e = s(W.k₁, W.k₂) then H.mult e - 1 else H.mult e) else 0 := by
  unfold SubObj.core SubObj.edges
  cases hh : W.hyper with
  | false =>
    simp only [Bool.false_eq_true, if_false, false_and]
    rfl
  | true =>
    simp only [if_true, true_and]
    show (if e = s(W.k₁, W.k₂) then (induce H W.atoms).mult e - 1 else (induce H W.atoms).mult e) = _
    show (if e = s(W.k₁, W.k₂) then (if e ∈ W.atoms.sym2 then H.mult e else 0) - 1 else
      (if e ∈ W.atoms.sym2 then H.mult e else 0)) = _
    by_cases h1 : e ∈ W.atoms.sym2 <;> by_cases h2 : e = s(W.k₁, W.k₂)
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
    · rw [if_pos h2, if_neg h1, if_neg h1]
    · rw [if_neg h2, if_neg h1, if_neg h1]

theorem core_mult_congr {H₁ H₂ : UMultigraph V} (W : SubObj V) {e : Sym2 V} (h : H₁.mult e = H₂.mult e) :
    (W.core H₁).mult e = (W.core H₂).mult e := by
  rw [core_mult, core_mult, h]

theorem core_mult_of_not_mem (H : UMultigraph V) (W : SubObj V) {e : Sym2 V} (h : e ∉ W.atoms.sym2) :
    (W.core H).mult e = 0 := by
  rw [core_mult, if_neg h]

theorem not_mem_sym2_of_disjoint {A B : Finset V} (hAB : Disjoint A B) {e : Sym2 V} (he : e ∈ A.sym2) :
    e ∉ B.sym2 := by
  intro hB
  induction e using Sym2.ind with
  | _ x y =>
  exact Finset.disjoint_left.mp hAB (Finset.mem_sym2_iff.mp he x (Sym2.mem_mk_left x y))
    (Finset.mem_sym2_iff.mp hB x (Sym2.mem_mk_left x y))

/-- **The closed formula for the removal of a disjoint family.** -/
theorem removeAll_eq (G : UMultigraph V) (Us : List (SubObj V)) (hsub : ∀ U ∈ Us, U.atoms ⊆ G.verts)
    (hdisj : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms)) :
    (removeAll G Us).verts = G.verts \ Checker.innerAll Us ∧
    ∀ e, (removeAll G Us).mult e = if e ∈ (G.verts \ Checker.innerAll Us).sym2 then
      G.mult e - (Us.map fun U => (U.core G).mult e).sum else 0 := by
  induction Us generalizing G with
  | nil =>
    refine ⟨by show G.verts = G.verts \ ∅; rw [Finset.sdiff_empty], fun e => ?_⟩
    simp only [removeAll, Checker.innerAll, List.foldr_nil, Finset.sdiff_empty, List.map_nil, List.sum_nil,
      Nat.sub_zero]
    split_ifs with h
    · rfl
    · by_contra hne; exact h (mem_sym2_of_mult_ne_zero G hne)
  | cons U Us ih =>
    have hU := hsub U List.mem_cons_self
    have hdU : ∀ W ∈ Us, Disjoint U.atoms W.atoms := (List.pairwise_cons.mp hdisj).1
    have hsubH : ∀ W ∈ Us, W.atoms ⊆ (removeSub G U).verts := by
      intro W hW x hx
      show x ∈ G.verts \ U.inner
      refine Finset.mem_sdiff.mpr ⟨hsub W (List.mem_cons_of_mem _ hW) hx, fun hxi => ?_⟩
      have : x ∈ U.atoms := (Finset.mem_erase.mp (Finset.mem_erase.mp hxi).2).2
      exact Finset.disjoint_left.mp (hdU W hW) this hx
    obtain ⟨hv, hm⟩ := ih (removeSub G U) hsubH (List.pairwise_cons.mp hdisj).2
    have hvert : (removeSub G U).verts \ Checker.innerAll Us = G.verts \ Checker.innerAll (U :: Us) := by
      show (G.verts \ U.inner) \ Checker.innerAll Us = G.verts \ (U.inner ∪ Checker.innerAll Us)
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union, not_or]; tauto
    refine ⟨by show (removeAll (removeSub G U) Us).verts = _; rw [hv, hvert], fun e => ?_⟩
    show (removeAll (removeSub G U) Us).mult e = _
    rw [hm e, hvert]
    split_ifs with he
    · have heU : e ∈ (G.verts \ U.inner).sym2 := by
        refine Finset.mem_sym2_iff.mpr fun x hx => ?_
        have := Finset.mem_sym2_iff.mp he x hx
        simp only [Finset.mem_sdiff] at this ⊢
        refine ⟨this.1, fun hxi => this.2 ?_⟩
        rw [mem_innerAll]; exact ⟨U, List.mem_cons_self, hxi⟩
      have hHm : (removeSub G U).mult e = G.mult e - (U.core G).mult e := by
        show (if e ∈ (G.verts \ U.inner).sym2 then G.mult e - (U.core G).mult e else 0) = _
        rw [if_pos heU]
      have hcores : (Us.map fun W => (W.core (removeSub G U)).mult e) = Us.map fun W => (W.core G).mult e := by
        refine List.map_congr_left fun W hW => ?_
        by_cases heW : e ∈ W.atoms.sym2
        · refine core_mult_congr W ?_
          rw [hHm, core_mult_of_not_mem G U (not_mem_sym2_of_disjoint (hdU W hW).symm heW), Nat.sub_zero]
        · rw [core_mult_of_not_mem _ W heW, core_mult_of_not_mem _ W heW]
      rw [hcores, hHm, List.map_cons, List.sum_cons, Nat.sub_sub]
    · rfl

/-- On a bond inside no member, the removal keeps every copy. -/
theorem mult_removeAll_of_out (G : UMultigraph V) (Us : List (SubObj V)) (hsub : ∀ U ∈ Us, U.atoms ⊆ G.verts)
    (hdisj : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms)) {e : Sym2 V}
    (he : e ∈ (G.verts \ Checker.innerAll Us).sym2) (hout : ∀ U ∈ Us, e ∉ U.atoms.sym2) :
    (removeAll G Us).mult e = G.mult e := by
  rw [(removeAll_eq G Us hsub hdisj).2 e, if_pos he]
  have : (Us.map fun U => (U.core G).mult e).sum = 0 := by
    rw [List.sum_eq_zero_iff]
    intro n hn
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hn
    exact core_mult_of_not_mem G W (hout W hW)
  rw [this, Nat.sub_zero]

/-- **N2's semantics removes more**: if `G` minus a disjoint family (N2's semantics) is connected, so is `G` minus
the family (sources' semantics). -/
theorem connected_removeAll_of_removeAllN (G : UMultigraph V) (Us : List (SubObj V))
    (hsub : ∀ U ∈ Us, U.atoms ⊆ G.verts) (hdisj : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms))
    (h : Connected (Checker.removeAllN G Us)) : Connected (removeAll G Us) := by
  obtain ⟨hv, -⟩ := removeAll_eq G Us hsub hdisj
  have hvN : (Checker.removeAllN G Us).verts = (removeAll G Us).verts := by rw [hv]; rfl
  have hstep : ∀ p q, AdjIn (Checker.removeAllN G Us) (Checker.removeAllN G Us).verts p q →
      AdjIn (removeAll G Us) (removeAll G Us).verts p q := by
    intro p q hpq
    rw [← hvN]
    refine ⟨hpq.1, hpq.2.1, ?_⟩
    have hm := hpq.2.2
    have hm' : (if s(p, q) ∈ (G.verts \ Checker.innerAll Us).sym2 ∧ ∀ U ∈ Us, s(p, q) ∉ U.atoms.sym2
        then G.mult s(p, q) else 0) ≠ 0 := hm
    split_ifs at hm' with hc
    · rw [mult_removeAll_of_out G Us hsub hdisj hc.1 hc.2]; exact hm'
    · exact absurd rfl hm'
  intro x hx y hy
  rw [← hvN] at hx hy
  have hr := h x hx y hy
  clear hx hy
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih => exact .tail ih (hstep _ _ hbc)

end WaveTurbulence.TVine.Struct
