/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.HingeStep4
/-! # The ladder selection claim (S3c)

From the (pairwise disjoint) maximal ladders, removing the hinge atoms one at a time splits each
affected ladder into at most two sub-ladders of consecutive rungs. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

theorem Lad.remove_atoms (layer : GBranch G.tree → ℕ) (H : Finset (GBranch G.tree)) :
    ∀ (l : List (Lad G)), Lad.Pw l → Lad.AllL l →
    ∃ l' : List (Lad G), Lad.Pw l' ∧ Lad.AllL l' ∧ (∀ ℓ' ∈ l', Disjoint ℓ'.atoms H) ∧
      (∀ ℓ' ∈ l', ∃ ℓ ∈ l, ℓ'.atoms ⊆ ℓ.atoms) ∧ Lad.TS l ≤ Lad.TS l' + 6 * H.card ∧
      Lad.IS layer l ≤ Lad.IS layer l' + 3 * H.card ∧ l'.length ≤ l.length + H.card := by
  induction H using Finset.induction_on with
  | empty =>
    intro l hP hL
    exact ⟨l, hP, hL, fun ℓ' _ => disjoint_empty_right _, fun ℓ' h => ⟨ℓ', h, subset_rfl⟩, by simp,
      by simp, by simp⟩
  | insert a H ha ih =>
    intro l hP hL
    obtain ⟨l₁, hP₁, hL₁, hD₁, hS₁, hT₁, hI₁, hN₁⟩ := ih l hP hL
    obtain ⟨l₂, hP₂, hL₂, ha₂, hS₂, hT₂, hI₂, hN₂⟩ := Lad.remove_atom layer l₁ hP₁ hL₁ a
    refine ⟨l₂, hP₂, hL₂, ?_, ?_, ?_, ?_, ?_⟩
    · intro ℓ' hℓ'
      rw [Finset.disjoint_insert_right]
      refine ⟨ha₂ ℓ' hℓ', ?_⟩
      obtain ⟨ℓ, hℓ, hsub⟩ := hS₂ ℓ' hℓ'
      exact (hD₁ ℓ hℓ).mono_left hsub
    · intro ℓ' hℓ'
      obtain ⟨ℓ, hℓ, hsub⟩ := hS₂ ℓ' hℓ'
      obtain ⟨ℓ0, hℓ0, hsub0⟩ := hS₁ ℓ hℓ
      exact ⟨ℓ0, hℓ0, hsub.trans hsub0⟩
    · rw [Finset.card_insert_of_notMem ha]; omega
    · rw [Finset.card_insert_of_notMem ha]; omega
    · rw [Finset.card_insert_of_notMem ha]; omega

end WaveTurbulence.CoarseSpliced
