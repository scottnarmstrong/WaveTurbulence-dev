/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiType

/-!
# Vine chains: basic bookkeeping

* `IsVineKindU.isBlockU`, `IsBlockU.verts_subset_of_induce`;
* `ChainU.subset`, `ChainU.ends_mem`, `ChainU.ne`;
* `deg_induce_mono`, `ChainU.deg_ge`: in a chain, the ends have degree ≥ 2 and the other atoms degree ≥ 4 inside the
  chain (loopless `H`);
* `ChainU.congr`: a chain survives a change of the graph that keeps all bonds inside its atom set.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

theorem IsVineKindU.isBlockU {k : EnlKind} {X : UMultigraph V} {p q : V} (h : IsVineKindU k X p q) :
    IsBlockU X p q := by
  cases k
  · exact h.1
  · exact h.1
  · exact h.1

/-- The atoms of a block induced in `H` are atoms of `H`. -/
theorem IsBlockU.verts_subset_of_induce {H : UMultigraph V} {T : Finset V} {p q : V}
    (h : IsBlockU (induce H T) p q) : T ⊆ H.verts := by
  intro v hv
  have hdeg : 2 ≤ deg (induce H T) v := by
    by_cases h1 : v = p
    · rw [h1, h.2.2.2.1]
    by_cases h2 : v = q
    · rw [h2, h.2.2.2.2.1]
    rw [h.2.2.2.2.2.1 v hv h1 h2]; omega
  by_contra hvH
  have h0 : deg (induce H T) v = 0 := by
    unfold deg
    have : ∀ w, (induce H T).mult s(v, w) = 0 := by
      intro w
      show (if s(v, w) ∈ T.sym2 then H.mult s(v, w) else 0) = 0
      split_ifs
      · exact mult_eq_zero_of_left H hvH w
      · rfl
    simp [this]
  omega

theorem deg_induce_mono (H : UMultigraph V) {S S' : Finset V} (hSS : S ⊆ S') {v : V} (hv : v ∈ S) :
    deg (induce H S) v ≤ deg (induce H S') v := by
  unfold deg
  rw [show (induce H S).verts = S from rfl, show (induce H S').verts = S' from rfl,
    induce_mult_of_mem H hv hv, induce_mult_of_mem H (hSS hv) (hSS hv)]
  have h1 : ∑ w ∈ S, (induce H S).mult s(v, w) = ∑ w ∈ S, (induce H S').mult s(v, w) :=
    Finset.sum_congr rfl fun w hw => by rw [induce_mult_of_mem H hv hw, induce_mult_of_mem H (hSS hv) (hSS hw)]
  have h2 : ∑ w ∈ S, (induce H S').mult s(v, w) ≤ ∑ w ∈ S', (induce H S').mult s(v, w) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSS fun _ _ _ => Nat.zero_le _
  omega

namespace ChainU

variable {H : UMultigraph V}

theorem subset {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks) : S ⊆ H.verts := by
  induction h with
  | single hv => exact hv.isBlockU.verts_subset_of_induce
  | append _ hv _ _ ih => exact Finset.union_subset ih hv.isBlockU.verts_subset_of_induce

theorem ends_mem {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks) : a ∈ S ∧ c ∈ S := by
  induction h with
  | single hv => exact ⟨hv.isBlockU.1, hv.isBlockU.2.1⟩
  | append _ hv _ _ ih => exact ⟨Finset.mem_union_left _ ih.1, Finset.mem_union_right _ hv.isBlockU.2.1⟩

theorem ne {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks) : a ≠ c := by
  cases h with
  | single hv => exact hv.isBlockU.2.2.1
  | append _ _ _ hac => exact hac

/-- Degrees inside a chain (loopless `H`): ends at least `2`, other atoms at least `4`. -/
theorem deg_ge (hl : H.Loopless) {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks) :
    2 ≤ deg (induce H S) a ∧ 2 ≤ deg (induce H S) c ∧
      ∀ v ∈ S, v ≠ a → v ≠ c → 4 ≤ deg (induce H S) v := by
  induction h with
  | @single T p q k hv =>
    have hB := hv.isBlockU
    refine ⟨by rw [hB.2.2.2.1], by rw [hB.2.2.2.2.1], fun v hv1 hv2 hv3 => by rw [hB.2.2.2.2.2.1 v hv1 hv2 hv3]⟩
  | @append S T a b c ks k hch hv hST hac ih =>
    have hB := hv.isBlockU
    have hbS : b ∈ S := hch.ends_mem.2
    have haS : a ∈ S := hch.ends_mem.1
    have hbT : b ∈ T := hB.1
    have hSU : S ⊆ S ∪ T := Finset.subset_union_left
    have hTU : T ⊆ S ∪ T := Finset.subset_union_right
    -- at the junction the two degrees add up
    have hjunc : deg (induce H S) b + deg (induce H T) b ≤ deg (induce H (S ∪ T)) b := by
      unfold deg
      simp only [show ∀ X : Finset V, (induce H X).verts = X from fun _ => rfl]
      rw [induce_mult_of_mem H hbS hbS, induce_mult_of_mem H hbT hbT, induce_mult_of_mem H (hSU hbS) (hSU hbS),
        hl b, add_zero, add_zero, add_zero]
      rw [Finset.sum_congr rfl fun w hw => induce_mult_of_mem H hbS hw,
        Finset.sum_congr rfl fun w hw => induce_mult_of_mem H hbT hw,
        Finset.sum_congr rfl fun w hw => induce_mult_of_mem H (hSU hbS) hw]
      have hsplit : ∑ w ∈ S ∪ T, H.mult s(b, w) = ∑ w ∈ S, H.mult s(b, w) + ∑ w ∈ T \ S, H.mult s(b, w) := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
      have hT : ∑ w ∈ T, H.mult s(b, w) = ∑ w ∈ T \ S, H.mult s(b, w) := by
        have : T = insert b (T \ S) := by
          ext x; simp only [Finset.mem_insert, Finset.mem_sdiff]
          constructor
          · intro hx; by_cases hxS : x ∈ S
            · left; have : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hxS, hx⟩; rw [hST] at this; simpa using this
            · exact Or.inr ⟨hx, hxS⟩
          · rintro (rfl | ⟨hx, -⟩); exacts [hbT, hx]
        have hbn : b ∉ T \ S := by simp [hbS]
        calc ∑ w ∈ T, H.mult s(b, w) = ∑ w ∈ insert b (T \ S), H.mult s(b, w) := by rw [← this]
          _ = ∑ w ∈ T \ S, H.mult s(b, w) := by rw [Finset.sum_insert hbn, hl b, zero_add]
      rw [hsplit, hT]
    refine ⟨?_, ?_, ?_⟩
    · exact ih.1.trans (deg_induce_mono H hSU haS)
    · rw [← hB.2.2.2.2.1]; exact deg_induce_mono H hTU hB.2.1
    · intro v hv hva hvc
      rcases Finset.mem_union.mp hv with hvS | hvT
      · by_cases hvb : v = b
        · subst hvb
          have := hB.2.2.2.1
          have := ih.2.1
          omega
        · exact (ih.2.2 v hvS hva hvb).trans (deg_induce_mono H hSU hvS)
      · by_cases hvb : v = b
        · subst hvb
          have := hB.2.2.2.1
          have := ih.2.1
          omega
        · rw [← hB.2.2.2.2.2.1 v hvT hvb hvc]; exact deg_induce_mono H hTU hvT

theorem induce_congr' {H' : UMultigraph V} {T : Finset V}
    (hm : ∀ u ∈ T, ∀ w ∈ T, H'.mult s(u, w) = H.mult s(u, w)) : induce H' T = induce H T := by
  apply ext
  · rfl
  · intro e
    show (if e ∈ T.sym2 then H'.mult e else 0) = (if e ∈ T.sym2 then H.mult e else 0)
    split_ifs with he
    · induction e using Sym2.ind with
      | h u w =>
        rw [Finset.mem_sym2_iff] at he
        exact hm u (he u (Sym2.mem_mk_left u w)) w (he w (Sym2.mem_mk_right u w))
    · rfl

/-- A chain survives a change of the graph that keeps all bonds inside its atom set. -/
theorem congr {H' : UMultigraph V} {S : Finset V} {a c : V} {ks : List EnlKind} (h : ChainU H S a c ks)
    (hm : ∀ u ∈ S, ∀ w ∈ S, H'.mult s(u, w) = H.mult s(u, w)) : ChainU H' S a c ks := by
  induction h with
  | single hv =>
    refine .single ?_
    rw [induce_congr' hm]; exact hv
  | append hch hv hST hac ih =>
    refine .append (ih fun u hu w hw => hm u (Finset.mem_union_left _ hu) w (Finset.mem_union_left _ hw)) ?_ hST hac
    rw [induce_congr' fun u hu w hw => hm u (Finset.mem_union_right _ hu) w (Finset.mem_union_right _ hw)]
    exact hv

end ChainU

end WaveTurbulence.TVine.Core
