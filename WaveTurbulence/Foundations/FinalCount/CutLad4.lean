/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutLad3
/-! Ladders under a cut, part 4 (FINALCOUNT-G2 step 2): the pieces of the ladder through `v`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The maximal ladder of the cut through the rungs `a..a+m'` of the ladder `(u, w)` of `M` through `v = u j₀`
(not containing the rung `j₀`) lies in the maximal ladder `S₀` of `M`. -/
theorem piece_exists (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    {m : ℕ} {u w : Fin (m + 1) → V} (hL : M.IsLadder u w) (hS₀ : Molecule.ladderAtoms u w ∈ M.maximalLadders)
    (j₀ : Fin (m + 1)) (hv : u j₀ = v) (a m' : ℕ) (hm' : 1 ≤ m') (h : a + m' ≤ m)
    (hr : a + m' < j₀.val ∨ j₀.val < a) :
    ∃ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
      Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h) ⊆ S := by
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp hL.2.1
  have hsub := IsLadder.sub M hL a m' hm' h
  have hnv : v ∉ Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h) := by
    intro hv'
    obtain ⟨i, hi | hi⟩ := (mem_ladderAtoms _ _ v).1 hv'
    · rw [subLad_apply] at hi
      have h1 := congrArg Fin.val (hu (hi.trans hv.symm))
      have := i.isLt
      simp only at h1; omega
    · rw [subLad_apply] at hi
      exact huw j₀ _ (hv.trans hi.symm)
  have hP : (M.cut v v₂ x₁ x₂).IsLadderSet (Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h)) :=
    (cut_isLadderSet_iff M hcd hdeg).2 ⟨⟨m', _, _, hsub, rfl⟩, hnv⟩
  obtain ⟨S, hS, hPS⟩ := exists_maximal_ladder_ge _ hP
  refine ⟨S, hS, ?_, hPS⟩
  obtain ⟨T, hT, hST⟩ := cut_maximal_sub M hcd hdeg hS
  have hTS₀ : T = Molecule.ladderAtoms u w := by
    by_contra hne
    have hdis := maximalLadders_pairwiseDisjoint_of_degree_le_four M hM hT hS₀ hne
    have hcard := card_ladderAtoms M hsub
    have hne' : (Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h)).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨x, hx⟩ := hne'
    exact Finset.disjoint_left.mp hdis (hST (hPS hx)) (ladderAtoms_sub_subset u w a m' h hx)
  exact hTS₀ ▸ hST

/-- **The ladder through `v` is replaced by at most two ladders, losing at most two rungs.** -/
theorem pieces_exist (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    {S₀ : Finset V} (hS₀ : S₀ ∈ M.maximalLadders) (hv : v ∈ S₀) :
    ∃ T : Finset (Finset V), (∀ S ∈ T, S ∈ (M.cut v v₂ x₁ x₂).maximalLadders ∧ S ⊆ S₀) ∧
      Molecule.ladderLength S₀ ≤ ∑ S ∈ T, Molecule.ladderLength S + 2 := by
  classical
  have hS₀' := hS₀
  rw [mem_maximalLadders_iff] at hS₀'
  obtain ⟨m, u, w, hL, rfl⟩ := hS₀'.1
  -- reduce to `v` on the first row
  obtain ⟨u, w, hL, hat, j₀, hj₀⟩ : ∃ u' w' : Fin (m + 1) → V, M.IsLadder u' w' ∧
      Molecule.ladderAtoms u' w' = Molecule.ladderAtoms u w ∧ ∃ j₀, u' j₀ = v := by
    obtain ⟨j, hj | hj⟩ := (mem_ladderAtoms u w v).1 hv
    · exact ⟨u, w, hL, rfl, j, hj⟩
    · exact ⟨w, u, sourceLadder_swap M hL, ladderAtoms_swap u w, j, hj⟩
  rw [← hat] at hS₀ ⊢
  have hlen := ladderLength_ladderAtoms M hL
  obtain ⟨hu, hw, huw⟩ := Sum.elim_injective.mp hL.2.1
  have hjm := j₀.isLt
  have pA : ∀ (hA : 2 ≤ j₀.val), ∃ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
      Molecule.ladderAtoms (subLad u 0 (j₀.val - 1) (by omega)) (subLad w 0 (j₀.val - 1) (by omega)) ⊆ S :=
    fun hA => piece_exists M hcd hdeg hM hL hS₀ j₀ hj₀ 0 (j₀.val - 1) (by omega) (by omega) (Or.inl (by omega))
  have pB : ∀ (hB : j₀.val + 2 ≤ m), ∃ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
      Molecule.ladderAtoms (subLad u (j₀.val + 1) (m - j₀.val - 1) (by omega))
        (subLad w (j₀.val + 1) (m - j₀.val - 1) (by omega)) ⊆ S :=
    fun hB => piece_exists M hcd hdeg hM hL hS₀ j₀ hj₀ (j₀.val + 1) (m - j₀.val - 1) (by omega) (by omega)
      (Or.inr (by omega))
  have cA : ∀ (hA : 2 ≤ j₀.val), (Molecule.ladderAtoms (subLad u 0 (j₀.val - 1) (by omega))
      (subLad w 0 (j₀.val - 1) (by omega))).card = 2 * (j₀.val - 1 + 1) :=
    fun hA => card_ladderAtoms M (IsLadder.sub M hL 0 (j₀.val - 1) (by omega) (by omega))
  have cB : ∀ (hB : j₀.val + 2 ≤ m), (Molecule.ladderAtoms (subLad u (j₀.val + 1) (m - j₀.val - 1) (by omega))
      (subLad w (j₀.val + 1) (m - j₀.val - 1) (by omega))).card = 2 * (m - j₀.val - 1 + 1) :=
    fun hB => card_ladderAtoms M (IsLadder.sub M hL (j₀.val + 1) (m - j₀.val - 1) (by omega) (by omega))
  by_cases hA : 2 ≤ j₀.val
  · obtain ⟨SA, hSA, hSA1, hSA2⟩ := pA hA
    have zA := ladderLength_ge_of_subset (cA hA) hSA2
    by_cases hB : j₀.val + 2 ≤ m
    · obtain ⟨SB, hSB, hSB1, hSB2⟩ := pB hB
      have zB := ladderLength_ge_of_subset (cB hB) hSB2
      by_cases e : SA = SB
      · subst e
        refine ⟨{SA}, ?_, ?_⟩
        · intro S hS; rw [Finset.mem_singleton] at hS; subst hS; exact ⟨hSA, hSA1⟩
        · rw [Finset.sum_singleton]
          have hdis := ladderAtoms_sub_disjoint hL.2.1 0 (j₀.val - 1) (j₀.val + 1) (m - j₀.val - 1)
            (by omega) (by omega) (by omega)
          have hc := Finset.card_le_card (Finset.union_subset hSA2 hSB2)
          rw [Finset.card_union_of_disjoint hdis, cA hA, cB hB] at hc
          unfold Molecule.ladderLength at *
          omega
      · refine ⟨{SA, SB}, ?_, ?_⟩
        · intro S hS
          rw [Finset.mem_insert, Finset.mem_singleton] at hS
          rcases hS with rfl | rfl
          · exact ⟨hSA, hSA1⟩
          · exact ⟨hSB, hSB1⟩
        · rw [Finset.sum_pair e]; omega
    · refine ⟨{SA}, ?_, ?_⟩
      · intro S hS; rw [Finset.mem_singleton] at hS; subst hS; exact ⟨hSA, hSA1⟩
      · rw [Finset.sum_singleton]; omega
  · by_cases hB : j₀.val + 2 ≤ m
    · obtain ⟨SB, hSB, hSB1, hSB2⟩ := pB hB
      have zB := ladderLength_ge_of_subset (cB hB) hSB2
      refine ⟨{SB}, ?_, ?_⟩
      · intro S hS; rw [Finset.mem_singleton] at hS; subst hS; exact ⟨hSB, hSB1⟩
      · rw [Finset.sum_singleton]; omega
    · refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty]; omega

end WaveTurbulence.FinalCount
