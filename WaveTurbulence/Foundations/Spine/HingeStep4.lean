/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.HingeStep3
/-! # Removing an atom from a list of disjoint ladders (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

variable {w : ℕ} {G : Garden w}

theorem Lad.remove_atom (layer : GBranch G.tree → ℕ) (l : List (Lad G)) (hP : Lad.Pw l)
    (hL : Lad.AllL l) (a : GBranch G.tree) :
    ∃ l' : List (Lad G), Lad.Pw l' ∧ Lad.AllL l' ∧ (∀ ℓ' ∈ l', a ∉ ℓ'.atoms) ∧
      (∀ ℓ' ∈ l', ∃ ℓ ∈ l, ℓ'.atoms ⊆ ℓ.atoms) ∧ Lad.TS l ≤ Lad.TS l' + 6 ∧
      Lad.IS layer l ≤ Lad.IS layer l' + 3 ∧ l'.length ≤ l.length + 1 := by
  by_cases hex : ∃ ℓ ∈ l, a ∈ ℓ.atoms
  swap
  · refine ⟨l, hP, hL, fun ℓ' h ha => hex ⟨ℓ', h, ha⟩, fun ℓ' h => ⟨ℓ', h, subset_rfl⟩, by omega, by omega,
      by omega⟩
  obtain ⟨ℓ, hℓ, ha⟩ := hex
  obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.mp hℓ
  have hℓL : ℓ.IsL := hL ℓ hℓ
  obtain ⟨k, hk⟩ := (Lad.mem_atoms_iff ℓ a).mp ha
  have hkle : (k : ℕ) ≤ ℓ.1 := Nat.lt_succ_iff.mp k.2
  obtain ⟨hps1, hps2⟩ := rangesAvoiding_props ℓ.1 k hkle
  obtain ⟨hpL, hpS, hpA, hpP⟩ := Lad.pieces_props ℓ hℓL k (rangesAvoiding ℓ.1 k) hps1 hps2
  obtain ⟨hn1, hn2, hn3⟩ := pieces_numbers layer ℓ hℓL k hkle
  -- structural facts about the original list
  rw [Lad.Pw, List.pairwise_append] at hP
  obtain ⟨hP1, hP2, hP12⟩ := hP
  rw [List.pairwise_cons] at hP2
  obtain ⟨hP2a, hP2b⟩ := hP2
  have hl₁ : ∀ x ∈ l₁, Disjoint x.atoms ℓ.atoms := fun x hx => hP12 x hx ℓ (List.mem_cons_self)
  have hl₂ : ∀ y ∈ l₂, Disjoint ℓ.atoms y.atoms := hP2a
  refine ⟨l₁ ++ (ℓ.pieces (rangesAvoiding ℓ.1 k) ++ l₂), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pairwise disjoint
    rw [Lad.Pw, List.pairwise_append]
    refine ⟨hP1, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hpP, hP2b, ?_⟩
      intro q hq y hy
      exact (hl₂ y hy).mono_left (hpS q hq)
    · intro x hx y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact (hl₁ x hx).mono_right (hpS y hy)
      · exact hP12 x hx y (List.mem_cons_of_mem _ hy)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL x (List.mem_append_left _ hx)
    · rcases List.mem_append.mp hx with hx | hx
      · exact hpL x hx
      · exact hL x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
  · intro x hx hax
    rcases List.mem_append.mp hx with hx | hx
    · exact Finset.disjoint_left.mp (hl₁ x hx) hax ha
    · rcases List.mem_append.mp hx with hx | hx
      · rcases hk with rfl | rfl
        · exact (hpA x hx).1 hax
        · exact (hpA x hx).2 hax
      · exact Finset.disjoint_left.mp (hl₂ x hx) ha hax
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨x, List.mem_append_left _ hx, subset_rfl⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨ℓ, List.mem_append_right _ List.mem_cons_self, hpS x hx⟩
      · exact ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ hx), subset_rfl⟩
  · simp only [Lad.TS, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hn1 ⊢
    omega
  · simp only [Lad.IS, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hn2 ⊢
    omega
  · simp only [List.length_append, List.length_cons, Lad.pieces, List.length_map] at hn3 ⊢
    omega

end WaveTurbulence.CoarseSpliced
