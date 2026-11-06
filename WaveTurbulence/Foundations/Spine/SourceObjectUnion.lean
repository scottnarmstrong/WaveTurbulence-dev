/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! Concatenating two vine chains at a single shared joint gives a vine chain. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem isSomeVine_ends {S : Finset V} {a b : V} (h : IsSomeVine M S a b) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  obtain ⟨X, hX⟩ := h
  exact ⟨hX.1.2.1, hX.1.2.2.1, hX.1.2.2.2.1⟩

theorem chain_ends {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  induction h with
  | single h => exact isSomeVine_ends h
  | append _ hT _ hac ih =>
    exact ⟨mem_union_left _ ih.1, mem_union_right _ (isSomeVine_ends hT).2.1, hac⟩

/-- Concatenation of chains sharing exactly the joining joint. -/
theorem chain_append_chain {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Chain M S a b n) (hT : Chain M T b c m) (hST : S ∩ T = {b}) :
    Chain M (S ∪ T) a c (n + m) := by
  induction hT generalizing S n with
  | @single T0 b0 c0 hv =>
    refine Chain.append hS hv hST ?_
    intro hac
    have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
    have : c0 ∈ S ∩ T0 := mem_inter.mpr ⟨hcS, (isSomeVine_ends hv).2.1⟩
    rw [hST] at this
    exact (isSomeVine_ends hv).2.2 (mem_singleton.mp this).symm
  | @append T1 T2 b0 p c0 k hT1 hv hT12 hbc ih =>
    have hbS := (chain_ends hS).2.1
    have hb1 := (chain_ends hT1).1
    have hsub1 : S ∩ T1 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_left
    have hsub2 : S ∩ T2 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_right
    rw [hST] at hsub1 hsub2
    have hS1 : S ∩ T1 = {b0} :=
      Subset.antisymm hsub1 (singleton_subset_iff.mpr (mem_inter.mpr ⟨hbS, hb1⟩))
    have hS2 : S ∩ T2 ⊆ {p} := by
      intro x hx
      have hxb : x = b0 := mem_singleton.mp (hsub2 hx)
      have hxT2 := (mem_inter.mp hx).2
      have : x ∈ T1 ∩ T2 := mem_inter.mpr ⟨hxb ▸ hb1, hxT2⟩
      rw [hT12] at this
      exact this
    have h1 := ih hS hS1
    have hne : a ≠ c0 := by
      intro hac
      have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
      have : c0 ∈ S ∩ (T1 ∪ T2) :=
        mem_inter.mpr ⟨hcS, mem_union_right _ (isSomeVine_ends hv).2.1⟩
      rw [hST] at this
      exact hbc (mem_singleton.mp this).symm
    have h2 := Chain.append h1 hv (by
      rw [union_inter_distrib_right, hT12]
      exact Subset.antisymm (union_subset hS2 (Subset.refl _))
        (subset_union_right)) hne
    rw [union_assoc] at h2
    exact h2

end WaveTurbulence.LGSpine.SourceVine
