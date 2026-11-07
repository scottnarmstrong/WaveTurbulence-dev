/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.AtomTriple
import Mathlib.Tactic

/-! # DH23 Lemma A.3(2): the triple count for every sign pattern without three equal signs

`atomTriple_bound` counts `q₁ − q₂ + q₃ = n_k`, `|‖q₁‖² − ‖q₂‖² + ‖q₃‖² − β| ≤ τ`. Every pattern of three signs that is not
constant reduces to this one by a global sign and a permutation of the three vectors.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.CountLemmas

section
variable {d : ℕ}

theorem card_le_of_inj_into {α β : Type*} (T : Finset α) (f : α → β) (hf : Function.Injective f) (S : Set β)
    (hS : ∀ t ∈ T, f t ∈ S) (hfin : S.Finite) : T.card ≤ S.ncard := by
  classical
  have h1 : (T.image f).card = T.card := card_image_of_injective _ hf
  have h2 := Set.ncard_le_ncard (show ((T.image f : Finset β) : Set β) ⊆ S from fun x hx => by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp (mem_coe.mp hx); exact hS t ht) hfin
  rw [Set.ncard_coe_finset] at h2
  omega

/-- A triple with signs `(e₁,e₂,e₃)`, not all equal. -/
def SignedTriple (L : ℝ) (e1 e2 e3 : ℤ) (c1 c2 c3 : Mom d) (nk : Fin d → ℤ) (β τ : ℝ)
    (t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) : Prop :=
  NearLattice L c1 t.1 ∧ NearLattice L c2 t.2.1 ∧ NearLattice L c3 t.2.2 ∧
    e1 • t.1 + e2 • t.2.1 + e3 • t.2.2 = nk ∧
    |(e1 : ℝ) * ‖latticePoint L t.1‖ ^ 2 + (e2 : ℝ) * ‖latticePoint L t.2.1‖ ^ 2 +
      (e3 : ℝ) * ‖latticePoint L t.2.2‖ ^ 2 - β| ≤ τ

theorem signedTriple_card_le (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ (e1 e2 e3 : ℤ), (e1 = 1 ∨ e1 = -1) → (e2 = 1 ∨ e2 = -1) →
      (e3 = 1 ∨ e3 = -1) → ¬ (e1 = e2 ∧ e2 = e3) → ∀ (c1 c2 c3 : Mom d) (nk : Fin d → ℤ) (β : ℝ)
      (T : Finset ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))),
      (∀ t ∈ T, SignedTriple L e1 e2 e3 c1 c2 c3 nk β (δ⁻¹ * L ^ (-2 * γ)) t) →
        (T.card : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) := by
  obtain ⟨C, L₀, h⟩ := atomTriple_bound d hd γ hγ
  refine ⟨C, L₀, fun L hL δ hδ e1 e2 e3 h1 h2 h3 hne c1 c2 c3 nk β T hT => ?_⟩
  have key : ∀ (f : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) → (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ))
      (a b c : Mom d) (nk' : Fin d → ℤ) (β' : ℝ), Function.Injective f →
      (∀ t ∈ T, f t ∈ atomTripleSet L a b c nk' β' (δ⁻¹ * L ^ (-2 * γ))) →
      (T.card : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) := by
    intro f a b c nk' β' hf hmem
    obtain ⟨hfin, hb⟩ := h L hL δ hδ β' nk' a b c
    have := card_le_of_inj_into T f hf _ hmem hfin
    exact le_trans (by exact_mod_cast this) hb
  have hinj1 : Function.Injective (fun t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (t.1, t.2.2, t.2.1)) := by
    intro s t h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
  have hinj2 : Function.Injective (fun t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => (t.2.1, t.1, t.2.2)) := by
    intro s t h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)
  have hinj0 : Function.Injective (fun t : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) => t) := fun s t h => h
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ hne
  · -- (1,1,-1): minority third
    refine key _ c1 c3 c2 nk β hinj1 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a1, a3, a2, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢; convert he using 2 <;> ring
  · -- (1,-1,1): minority second
    refine key _ c1 c2 c3 nk β hinj0 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a1, a2, a3, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢; convert he using 2 <;> ring
  · -- (1,-1,-1): minority first, global sign
    refine key _ c2 c1 c3 (-nk) (-β) hinj2 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a2, a1, a3, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢
      rw [← abs_neg] at he; convert he using 2 <;> ring
  · -- (-1,1,1)
    refine key _ c2 c1 c3 nk β hinj2 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a2, a1, a3, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢; convert he using 2 <;> ring
  · -- (-1,1,-1): minority second, global sign
    refine key _ c1 c2 c3 (-nk) (-β) hinj0 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a1, a2, a3, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢
      rw [← abs_neg] at he; convert he using 2 <;> ring
  · -- (-1,-1,1)
    refine key _ c1 c3 c2 (-nk) (-β) hinj1 fun t ht => ?_
    obtain ⟨a1, a2, a3, hm, he⟩ := hT t ht
    refine ⟨a1, a3, a2, ?_, ?_⟩
    · simp only [one_smul, neg_smul] at hm ⊢; rw [← hm]; abel
    · simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul] at he ⊢
      rw [← abs_neg] at he; convert he using 2 <;> ring
  · exact absurd ⟨rfl, rfl⟩ hne

end
end WaveTurbulence.FinalCountG8
