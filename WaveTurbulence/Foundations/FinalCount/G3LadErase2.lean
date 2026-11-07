/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3LadErase1
/-! **FINALCOUNT-G3 (R29 item 6, O3), part 2: erasing one atom costs at most two rungs of its ladder** (set-erasure copy of CutLad4/5).
`ladderProd_le_erase1`: `∏_{M.max} X^z ≤ K² ∏_{(M - v).max} X^z` when `1 ≤ X ≤ K` and sub-ladders inherit the weight. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LadderDisjoint

universe u w'
variable {V : Type u} [DecidableEq V] {D : Type w'} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V}

/-- The maximal ladder of the cut through the rungs `a..a+m'` of the ladder `(u, w)` of `M` through `v = u j₀`
(not containing the rung `j₀`) lies in the maximal ladder `S₀` of `M`. -/
theorem erase_piece_exists (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    {m : ℕ} {u w : Fin (m + 1) → V} (hL : M.IsLadder u w) (hS₀ : Molecule.ladderAtoms u w ∈ M.maximalLadders)
    (j₀ : Fin (m + 1)) (hv : u j₀ = v) (a m' : ℕ) (hm' : 1 ≤ m') (h : a + m' ≤ m)
    (hr : a + m' < j₀.val ∨ j₀.val < a) :
    ∃ S ∈ (eraseSet M {v}).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
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
  have hP : (eraseSet M {v}).IsLadderSet (Molecule.ladderAtoms (subLad u a m' h) (subLad w a m' h)) :=
    (eraseSet_isLadderSet_iff M).2 ⟨⟨m', _, _, hsub, rfl⟩, Finset.disjoint_singleton_right.2 hnv⟩
  obtain ⟨S, hS, hPS⟩ := exists_maximal_ladder_ge _ hP
  refine ⟨S, hS, ?_, hPS⟩
  obtain ⟨T, hT, hST⟩ := erase_maximal_sub M hS
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
theorem erase_pieces_exist (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    {S₀ : Finset V} (hS₀ : S₀ ∈ M.maximalLadders) (hv : v ∈ S₀) :
    ∃ T : Finset (Finset V), (∀ S ∈ T, S ∈ (eraseSet M {v}).maximalLadders ∧ S ⊆ S₀) ∧
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
  have pA : ∀ (hA : 2 ≤ j₀.val), ∃ S ∈ (eraseSet M {v}).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
      Molecule.ladderAtoms (subLad u 0 (j₀.val - 1) (by omega)) (subLad w 0 (j₀.val - 1) (by omega)) ⊆ S :=
    fun hA => erase_piece_exists M hM hL hS₀ j₀ hj₀ 0 (j₀.val - 1) (by omega) (by omega) (Or.inl (by omega))
  have pB : ∀ (hB : j₀.val + 2 ≤ m), ∃ S ∈ (eraseSet M {v}).maximalLadders, S ⊆ Molecule.ladderAtoms u w ∧
      Molecule.ladderAtoms (subLad u (j₀.val + 1) (m - j₀.val - 1) (by omega))
        (subLad w (j₀.val + 1) (m - j₀.val - 1) (by omega)) ⊆ S :=
    fun hB => erase_piece_exists M hM hL hS₀ j₀ hj₀ (j₀.val + 1) (m - j₀.val - 1) (by omega) (by omega)
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


/-- **Ladder comparison for a cut (F-FC-3).** If the weights satisfy `1 ≤ X ≤ K` and the sub-ladders of a
maximal ladder inherit its weight, the ladder factor of `𝔄_pre` is at most `K²` times that of `𝔄_pos`. -/
theorem ladderProd_le_erase1 (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (X : Finset V → ℝ) (K : ℝ) (hX1 : ∀ S, 1 ≤ X S) (hXK : ∀ S, X S ≤ K)
    (hP : ∀ S' ∈ (eraseSet M {v}).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → X S' = X S) :
    ∏ S ∈ M.maximalLadders, X S ^ Molecule.ladderLength S ≤
      K ^ 2 * ∏ S ∈ (eraseSet M {v}).maximalLadders, X S ^ Molecule.ladderLength S := by
  classical
  set A := M.maximalLadders.filter (fun S => v ∉ S) with hA
  have hAC : A ⊆ (eraseSet M {v}).maximalLadders := fun S hS => by
    rw [hA, Finset.mem_filter] at hS
    exact erase_maximal_of_avoid M hS.1 (Finset.disjoint_singleton_right.2 hS.2)
  have hpos : ∀ S, 1 ≤ X S ^ Molecule.ladderLength S := fun S => one_le_pow₀ (hX1 S)
  have hK1 : 1 ≤ K := (hX1 ∅).trans (hXK ∅)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  have hCpos : 0 ≤ ∏ S ∈ (eraseSet M {v}).maximalLadders, X S ^ Molecule.ladderLength S :=
    Finset.prod_nonneg fun S _ => zero_le_one.trans (hpos S)
  by_cases hex : ∃ S₀ ∈ M.maximalLadders, v ∈ S₀
  · obtain ⟨S₀, hS₀, hvS₀⟩ := hex
    have hMeq : M.maximalLadders = insert S₀ A := by
      ext S
      rw [Finset.mem_insert, hA, Finset.mem_filter]
      constructor
      · intro hS
        by_cases hv : v ∈ S
        · left
          by_contra hne
          exact Finset.disjoint_left.mp (maximalLadders_pairwiseDisjoint_of_degree_le_four M hM hS hS₀ hne) hv hvS₀
        · exact Or.inr ⟨hS, hv⟩
      · rintro (rfl | ⟨hS, _⟩)
        · exact hS₀
        · exact hS
    have hS₀A : S₀ ∉ A := fun h => (Finset.mem_filter.mp h).2 hvS₀
    obtain ⟨T, hT, hlen⟩ := erase_pieces_exist M hM hS₀ hvS₀
    have hTA : Disjoint T A := by
      rw [Finset.disjoint_left]
      intro S hS hSA
      have hSA' := Finset.mem_filter.mp hSA
      have hSS₀ := (hT S hS).2
      have := (mem_maximalLadders_iff M).1 hS₀
      have h2 := ((mem_maximalLadders_iff M).1 hSA'.1).2 S₀ this.1 hSS₀
      exact hSA'.2 (h2 ▸ hvS₀)
    have hTC : T ∪ A ⊆ (eraseSet M {v}).maximalLadders :=
      Finset.union_subset (fun S hS => (hT S hS).1) hAC
    have hX₀ : ∀ S ∈ T, X S = X S₀ := fun S hS => hP S (hT S hS).1 S₀ hS₀ (hT S hS).2
    have hprodT : ∏ S ∈ T, X S ^ Molecule.ladderLength S = X S₀ ^ ∑ S ∈ T, Molecule.ladderLength S := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun S hS => by rw [hX₀ S hS]
    have hC : (∏ S ∈ T, X S ^ Molecule.ladderLength S) * ∏ S ∈ A, X S ^ Molecule.ladderLength S ≤
        ∏ S ∈ (eraseSet M {v}).maximalLadders, X S ^ Molecule.ladderLength S := by
      rw [← Finset.prod_union hTA]
      exact prod_mono_real hTC _ (fun S _ => hpos S)
    rw [hMeq, Finset.prod_insert hS₀A]
    set sg := ∑ S ∈ T, Molecule.ladderLength S
    have hX₀1 := hX1 S₀
    have hX₀K := hXK S₀
    have h1 : X S₀ ^ Molecule.ladderLength S₀ ≤ K ^ 2 * X S₀ ^ sg := by
      calc X S₀ ^ Molecule.ladderLength S₀ ≤ X S₀ ^ (sg + 2) := pow_le_pow_right₀ hX₀1 hlen
        _ = X S₀ ^ 2 * X S₀ ^ sg := by ring
        _ ≤ K ^ 2 * X S₀ ^ sg := by
          have : X S₀ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hX₀1) hX₀K 2
          have h0 : 0 ≤ X S₀ ^ sg := pow_nonneg (zero_le_one.trans hX₀1) _
          nlinarith
    have hAnn : 0 ≤ ∏ S ∈ A, X S ^ Molecule.ladderLength S :=
      Finset.prod_nonneg fun S _ => zero_le_one.trans (hpos S)
    rw [hprodT] at hC
    calc X S₀ ^ Molecule.ladderLength S₀ * ∏ S ∈ A, X S ^ Molecule.ladderLength S
        ≤ (K ^ 2 * X S₀ ^ sg) * ∏ S ∈ A, X S ^ Molecule.ladderLength S :=
          mul_le_mul_of_nonneg_right h1 hAnn
      _ = K ^ 2 * (X S₀ ^ sg * ∏ S ∈ A, X S ^ Molecule.ladderLength S) := by ring
      _ ≤ K ^ 2 * _ := mul_le_mul_of_nonneg_left hC (by positivity)
  · push Not at hex
    have hMA : M.maximalLadders ⊆ A := fun S hS => by
      rw [hA, Finset.mem_filter]; exact ⟨hS, hex S hS⟩
    calc ∏ S ∈ M.maximalLadders, X S ^ Molecule.ladderLength S
        ≤ ∏ S ∈ (eraseSet M {v}).maximalLadders, X S ^ Molecule.ladderLength S :=
          prod_mono_real (hMA.trans hAC) _ (fun S _ => hpos S)
      _ ≤ K ^ 2 * _ := by nlinarith


end WaveTurbulence.FinalCountG3
