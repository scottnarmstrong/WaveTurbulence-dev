/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Parity
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Del

/-!
# Induced sub-multigraphs, closed sets, symmetries of 2-cut rungs and sub-objects

* `induce_mult_of_mem`, `deg_induce_add`: `deg G u = deg (induce G S) u + Σ_{w ∉ S} mult(u, w)`;
* `eq_of_closed'`: a nonempty set closed under adjacency inside a connected set is all of it;
* `IsRungAt.swapAB`, `IsRungAt.swapPoles`, `IsRungOf.swapAB`, `IsRungOf.swapPoles`;
* `SubObj.swap` and `IsSubObjU.swap` (exchanging the joints of a sub-object).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

variable {V : Type*} [DecidableEq V]

theorem induce_mult_of_mem (G : UMultigraph V) {S : Finset V} {u w : V} (hu : u ∈ S) (hw : w ∈ S) :
    (induce G S).mult s(u, w) = G.mult s(u, w) := by
  show (if s(u, w) ∈ S.sym2 then G.mult s(u, w) else 0) = _
  rw [if_pos]
  rw [Finset.mem_sym2_iff]; intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

theorem induce_mult_of_not_mem (G : UMultigraph V) {S : Finset V} {u w : V} (hw : w ∉ S) :
    (induce G S).mult s(u, w) = 0 := by
  show (if s(u, w) ∈ S.sym2 then G.mult s(u, w) else 0) = _
  rw [if_neg]
  rw [Finset.mem_sym2_iff]; intro h; exact hw (h w (Sym2.mem_mk_right u w))

/-- The degree in an induced sub-multigraph misses exactly the bonds leaving `S`. -/
theorem deg_induce_add (G : UMultigraph V) {S : Finset V} (hS : S ⊆ G.verts) {u : V} (hu : u ∈ S) :
    deg G u = deg (induce G S) u + ∑ w ∈ G.verts \ S, G.mult s(u, w) := by
  unfold deg
  rw [show (induce G S).verts = S from rfl, induce_mult_of_mem G hu hu,
    Finset.sum_congr rfl fun w hw => induce_mult_of_mem G hu hw, ← Finset.sum_sdiff hS]
  ring

/-- A nonempty set closed under adjacency inside a connected atom set is all of it. -/
theorem eq_of_closed' {G : UMultigraph V} {K S : Finset V} (hK : ConnOn G K) (hS : S ⊆ K) (hne : S.Nonempty)
    (hcl : ∀ u ∈ S, ∀ w ∈ K, G.mult s(u, w) ≠ 0 → w ∈ S) : S = K := by
  apply Finset.Subset.antisymm hS
  intro w hw
  obtain ⟨s₀, hs₀⟩ := hne
  suffices H : ∀ v, Relation.ReflTransGen (AdjIn G K) s₀ v → v ∈ S from H w (hK s₀ (hS hs₀) w hw)
  intro v hv
  induction hv with
  | refl => exact hs₀
  | tail _ hstep ih => exact hcl _ ih _ hstep.2.1 hstep.2.2

/-! ## Symmetries -/

theorem IsRungAt.swapAB {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungAt G a b xm xp ym yp Km Kp) : IsRungAt G b a ym yp xm xp Km Kp where
  ne := h.ne.symm
  a_mem := h.b_mem
  b_mem := h.a_mem
  mult_ab := by rw [Sym2.eq_swap]; exact h.mult_ab
  disj := h.disj
  union := by rw [h.union]; exact Finset.erase_right_comm
  connm := h.connm
  connp := h.connp
  noBond := h.noBond
  xm_mem := h.ym_mem
  xp_mem := h.yp_mem
  ym_mem := h.xm_mem
  yp_mem := h.xp_mem
  a_xm := h.b_ym
  a_xp := h.b_yp
  b_ym := h.a_xm
  b_yp := h.a_xp
  a_other := h.b_other
  b_other := h.a_other

theorem IsRungAt.swapPoles {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungAt G a b xm xp ym yp Km Kp) : IsRungAt G a b xp xm yp ym Kp Km where
  ne := h.ne
  a_mem := h.a_mem
  b_mem := h.b_mem
  mult_ab := h.mult_ab
  disj := h.disj.symm
  union := by rw [Finset.union_comm]; exact h.union
  connm := h.connp
  connp := h.connm
  noBond u hu w hw := by rw [Sym2.eq_swap]; exact h.noBond w hw u hu
  xm_mem := h.xp_mem
  xp_mem := h.xm_mem
  ym_mem := h.yp_mem
  yp_mem := h.ym_mem
  a_xm := h.a_xp
  a_xp := h.a_xm
  b_ym := h.b_yp
  b_yp := h.b_ym
  a_other z h1 h2 h3 := h.a_other z h1 h3 h2
  b_other z h1 h2 h3 := h.b_other z h1 h3 h2

theorem IsRungOf.swapAB {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp) : IsRungOf G j₁ j₂ b a ym yp xm xp Km Kp :=
  ⟨h.1.swapAB, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩

theorem IsRungOf.swapPoles {G : UMultigraph V} {j₁ j₂ a b xm xp ym yp : V} {Km Kp : Finset V}
    (h : IsRungOf G j₁ j₂ a b xm xp ym yp Km Kp) : IsRungOf G j₁ j₂ a b xp xm yp ym Kp Km :=
  ⟨h.1.swapPoles, h.2⟩

theorem IsBlockU.swap {G : UMultigraph V} {j₁ j₂ : V} (h : IsBlockU G j₁ j₂) : IsBlockU G j₂ j₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h2, h1, h3.symm, h5, h4, fun v hv a b => h6 v hv b a, h7⟩

theorem SubObj.core_verts (G : UMultigraph V) (U : SubObj V) : (U.core G).verts = U.atoms := by
  unfold SubObj.core; split <;> rfl

/-- A sub-object with its joints exchanged. -/
def SubObj.swap (U : SubObj V) : SubObj V := ⟨U.atoms, U.k₂, U.k₁, U.hyper⟩

theorem SubObj.core_swap (G : UMultigraph V) (U : SubObj V) : U.swap.core G = U.core G := by
  unfold SubObj.core SubObj.swap SubObj.edges
  simp only [Sym2.eq_swap (a := U.k₂)]

theorem IsSubObjU.swap {G : UMultigraph V} {U : SubObj V} (h : IsSubObjU G U) : IsSubObjU G U.swap := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun hh => by rw [Sym2.eq_swap]; exact h2 hh, ?_⟩
  rw [SubObj.core_swap]
  exact h3.swap

end WaveTurbulence.TVine.Core
