/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev2
/-! **FINALCOUNT-G3 (R29 item 3): cluster additivity.**  For pairwise disjoint clusters `𝒦` with no bond between two distinct clusters and
`T = ⋃ 𝒦`: `e_T = ∑ e_K`, `intDart_T = ∑ intDart_K`, `|T| = ∑ |K|`; hence from `2R' + 4|T| ≤ 2R + tch(T)`:
`R' ≤ R + ∑_K (e_K + χ_K - 1 - s_K)` with `χ_K = ib_K - s_K + 1`, `ib_K = intDart_K / 2`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- Clusters: pairwise disjoint, no bond between two distinct ones. -/
structure Clusters (M : Molecule V D) (𝒦 : Finset (Finset V)) : Prop where
  disj : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K'
  nobond : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ∀ x : D, M.atom x ∈ K → M.atom (M.mate x) ∉ K'

theorem eDart_biUnion {𝒦 : Finset (Finset V)} (h : Clusters M 𝒦) :
    eDart M (𝒦.biUnion id) = ∑ K ∈ 𝒦, eDart M K := by
  unfold eDart
  have : (Finset.univ.filter fun x : D => M.atom x ∈ 𝒦.biUnion id ∧ M.atom (M.mate x) ∉ 𝒦.biUnion id) =
      𝒦.biUnion (fun K => Finset.univ.filter fun x : D => M.atom x ∈ K ∧ M.atom (M.mate x) ∉ K) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, id]
    constructor
    · rintro ⟨⟨K, hK, hxK⟩, hn⟩
      exact ⟨K, hK, hxK, fun hm => hn ⟨K, hK, hm⟩⟩
    · rintro ⟨K, hK, hxK, hn⟩
      refine ⟨⟨K, hK, hxK⟩, ?_⟩
      rintro ⟨K', hK', hm⟩
      by_cases e : K = K'
      · subst e; exact hn hm
      · exact h.nobond K hK K' hK' e x hxK hm
  rw [this, Finset.card_biUnion]
  intro K hK K' hK' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact Finset.disjoint_left.1 (h.disj K hK K' hK' hne) hx.1 hx'.1

end WaveTurbulence.FinalCountG3
