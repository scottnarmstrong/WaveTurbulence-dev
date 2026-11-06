/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
/-! Every finite simple graph has at least `|V| - (number of components)` edges (the circuit rank is
nonnegative): the first edge of a shortest walk to a chosen root of its component is an injection of the
non-root vertices into the edges. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SimpleGraph

theorem card_le_edgeSet_add_components {V : Type*} [Fintype V] (H : SimpleGraph V) :
    Fintype.card V ≤ Nat.card H.edgeSet + Nat.card H.ConnectedComponent := by
  classical
  haveI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let rootC : H.ConnectedComponent → V := fun c => c.out
  let rt : V → V := fun v => rootC (H.connectedComponentMk v)
  have hrt : ∀ v, H.Reachable v (rt v) := by
    intro v
    have h : H.connectedComponentMk (rt v) = H.connectedComponentMk v := Quot.out_eq _
    exact (ConnectedComponent.exact h).symm
  have hex : ∀ v : V, ∃ u, v ≠ rt v → H.Adj v u ∧ H.dist u (rt v) + 1 ≤ H.dist v (rt v) := by
    intro v
    by_cases hv : v = rt v
    · exact ⟨v, fun h => (h hv).elim⟩
    · have key : ∀ (r : V), v ≠ r → ∀ (p : H.Walk v r), p.length = H.dist v r →
          ∃ u, H.Adj v u ∧ H.dist u r + 1 ≤ H.dist v r := by
        intro r hvr p hp
        cases p with
        | nil => exact (hvr rfl).elim
        | cons hadj q =>
          rename_i u'
          refine ⟨u', hadj, ?_⟩
          have := H.dist_le q
          simp only [Walk.length_cons] at hp
          omega
      obtain ⟨p, hp⟩ := (hrt v).exists_walk_length_eq_dist
      obtain ⟨u, hu⟩ := key (rt v) hv p hp
      exact ⟨u, fun _ => hu⟩
  choose par hpar using hex
  have hsame : ∀ v, rt (par v) = rt v ∨ v = rt v := by
    intro v
    by_cases hv : v = rt v
    · exact Or.inr hv
    · left
      have hadj := (hpar v hv).1
      have h : H.connectedComponentMk (par v) = H.connectedComponentMk v :=
        (ConnectedComponent.eq.mpr hadj.symm.reachable)
      show rootC (H.connectedComponentMk (par v)) = rootC (H.connectedComponentMk v)
      rw [h]
  let Rset : Finset V := Finset.univ.image rootC
  let S : Finset V := Finset.univ \ Rset
  have hS : ∀ v ∈ S, v ≠ rt v := by
    intro v hv hveq
    apply (Finset.mem_sdiff.mp hv).2
    exact Finset.mem_image.mpr ⟨H.connectedComponentMk v, Finset.mem_univ _, hveq.symm⟩
  have hinj : S.card ≤ H.edgeFinset.card := by
    apply Finset.card_le_card_of_injOn (fun v => s(v, par v))
    · intro v hv
      have := (hpar v (hS v hv)).1
      simpa using this
    · intro v hv w hw hvw
      have hvw' : s(v, par v) = s(w, par w) := hvw
      rw [Sym2.eq_iff] at hvw'
      rcases hvw' with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso
        have hv' := hpar v (hS v hv)
        have hw' := hpar w (hS w hw)
        have hrtw : rt w = rt v := by
          have := hsame w
          rcases this with h | h
          · rw [← h, ← h1]
          · exact (hS w hw h).elim
        rw [← h1] at hw'
        have e2 : H.dist w (rt v) + 1 ≤ H.dist v (rt v) := by
          have := hv'.2
          rw [h2] at this
          exact this
        have e1 : H.dist v (rt v) + 1 ≤ H.dist w (rt v) := by
          have := hw'.2
          rw [hrtw] at this
          exact this
        omega
  have hR : Rset.card ≤ Nat.card H.ConnectedComponent := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_image_le.trans (by simp)
  have hcardS : S.card + Rset.card = Fintype.card V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
  have hE : H.edgeFinset.card = Nat.card H.edgeSet := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

end WaveTurbulence.LGSpine
