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

theorem intDart_biUnion {𝒦 : Finset (Finset V)} (h : Clusters M 𝒦) :
    intDart M (𝒦.biUnion id) = ∑ K ∈ 𝒦, intDart M K := by
  unfold intDart
  have : (Finset.univ.filter fun x : D => M.atom x ∈ 𝒦.biUnion id ∧ M.atom (M.mate x) ∈ 𝒦.biUnion id) =
      𝒦.biUnion (fun K => Finset.univ.filter fun x : D => M.atom x ∈ K ∧ M.atom (M.mate x) ∈ K) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, id]
    constructor
    · rintro ⟨⟨K, hK, hxK⟩, ⟨K', hK', hm⟩⟩
      by_cases e : K = K'
      · subst e; exact ⟨K, hK, hxK, hm⟩
      · exact absurd hm (h.nobond K hK K' hK' e x hxK)
    · rintro ⟨K, hK, hxK, hm⟩
      exact ⟨⟨K, hK, hxK⟩, ⟨K, hK, hm⟩⟩
  rw [this, Finset.card_biUnion]
  intro K hK K' hK' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact Finset.disjoint_left.1 (h.disj K hK K' hK' hne) hx.1 hx'.1

theorem card_biUnion_clusters {𝒦 : Finset (Finset V)} (h : Clusters M 𝒦) :
    (𝒦.biUnion id).card = ∑ K ∈ 𝒦, K.card := by
  rw [Finset.card_biUnion]
  · rfl
  · intro K hK K' hK' hne
    exact h.disj K hK K' hK' hne

theorem intDart_even (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) {K : Finset V} (hK : K ⊆ M.atoms) :
    2 * (intDart M K / 2) = intDart M K := by
  obtain ⟨ib, hib, -⟩ := circuitRank_eraseSet hnl hK
  omega

/-- **Cluster additivity of the index of Operation 5.** -/
theorem cluster_index {𝒦 : Finset (Finset V)} (h : Clusters M 𝒦) (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hsub : ∀ K ∈ 𝒦, K ⊆ M.atoms) {R R' : ℕ}
    (hR : 2 * (R' : ℤ) + 4 * ((𝒦.biUnion id).card : ℤ) ≤ 2 * (R : ℤ) + (tch M (𝒦.biUnion id) : ℤ)) :
    (R' : ℤ) ≤ R + ∑ K ∈ 𝒦, ((eDart M K : ℤ) + (((intDart M K / 2 : ℕ) : ℤ) - K.card + 1) - 1 - K.card) := by
  have h1 := tch_eq M (𝒦.biUnion id)
  rw [eDart_biUnion h, intDart_biUnion h] at h1
  rw [card_biUnion_clusters h] at hR
  have h2 : ∑ K ∈ 𝒦, ((eDart M K : ℤ) + (((intDart M K / 2 : ℕ) : ℤ) - K.card + 1) - 1 - K.card) =
      ∑ K ∈ 𝒦, ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - 2 * K.card) := by
    refine Finset.sum_congr rfl fun K hK => ?_
    ring
  have h3 : 2 * ∑ K ∈ 𝒦, ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - 2 * K.card) =
      ∑ K ∈ 𝒦, (2 * (eDart M K : ℤ) + (intDart M K : ℤ) - 4 * (K.card : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    have := intDart_even hnl (hsub K hK)
    omega
  have h4 : ∑ K ∈ 𝒦, (2 * (eDart M K : ℤ) + (intDart M K : ℤ) - 4 * (K.card : ℤ)) =
      2 * ∑ K ∈ 𝒦, (eDart M K : ℤ) + ∑ K ∈ 𝒦, (intDart M K : ℤ) - 4 * ∑ K ∈ 𝒦, (K.card : ℤ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h5 : (tch M (𝒦.biUnion id) : ℤ) = 2 * ∑ K ∈ 𝒦, (eDart M K : ℤ) + ∑ K ∈ 𝒦, (intDart M K : ℤ) := by
    rw [h1]; push_cast; rfl
  have hc3 : ((∑ K ∈ 𝒦, K.card : ℕ) : ℤ) = ∑ K ∈ 𝒦, (K.card : ℤ) := by push_cast; rfl
  rw [hc3] at hR
  rw [h2]
  linarith

end WaveTurbulence.FinalCountG3
