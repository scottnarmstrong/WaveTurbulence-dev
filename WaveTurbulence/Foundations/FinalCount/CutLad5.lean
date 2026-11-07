/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutLad4
/-! Ladders under a cut, part 5 (FINALCOUNT-G2 step 2, F-FC-3): the ladder factor of `𝔄` changes by at most `K²`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LadderDisjoint

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem prod_mono_real {ι : Type*} [DecidableEq ι] {s t : Finset ι} (hs : s ⊆ t) (f : ι → ℝ)
    (hf : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hs]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := by
    refine Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => by nlinarith) le_rfl ?_
    exact fun i hi => hf i (Finset.mem_sdiff.mp hi).1
  have h2 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => zero_le_one.trans (hf i (hs hi))
  nlinarith

/-- **Ladder comparison for a cut (F-FC-3).** If the weights satisfy `1 ≤ X ≤ K` and the sub-ladders of a
maximal ladder inherit its weight, the ladder factor of `𝔄_pre` is at most `K²` times that of `𝔄_pos`. -/
theorem ladderProd_le (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (X : Finset V → ℝ) (K : ℝ) (hX1 : ∀ S, 1 ≤ X S) (hXK : ∀ S, X S ≤ K)
    (hP : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → X S' = X S) :
    ∏ S ∈ M.maximalLadders, X S ^ Molecule.ladderLength S ≤
      K ^ 2 * ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, X S ^ Molecule.ladderLength S := by
  classical
  set A := M.maximalLadders.filter (fun S => v ∉ S) with hA
  have hAC : A ⊆ (M.cut v v₂ x₁ x₂).maximalLadders := fun S hS => by
    rw [hA, Finset.mem_filter] at hS
    exact cut_maximal_of_avoid M hcd hdeg hS.1 hS.2
  have hpos : ∀ S, 1 ≤ X S ^ Molecule.ladderLength S := fun S => one_le_pow₀ (hX1 S)
  have hK1 : 1 ≤ K := (hX1 ∅).trans (hXK ∅)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK1
  have hCpos : 0 ≤ ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, X S ^ Molecule.ladderLength S :=
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
    obtain ⟨T, hT, hlen⟩ := pieces_exist M hcd hdeg hM hS₀ hvS₀
    have hTA : Disjoint T A := by
      rw [Finset.disjoint_left]
      intro S hS hSA
      have hSA' := Finset.mem_filter.mp hSA
      have hSS₀ := (hT S hS).2
      have := (mem_maximalLadders_iff M).1 hS₀
      have h2 := ((mem_maximalLadders_iff M).1 hSA'.1).2 S₀ this.1 hSS₀
      exact hSA'.2 (h2 ▸ hvS₀)
    have hTC : T ∪ A ⊆ (M.cut v v₂ x₁ x₂).maximalLadders :=
      Finset.union_subset (fun S hS => (hT S hS).1) hAC
    have hX₀ : ∀ S ∈ T, X S = X S₀ := fun S hS => hP S (hT S hS).1 S₀ hS₀ (hT S hS).2
    have hprodT : ∏ S ∈ T, X S ^ Molecule.ladderLength S = X S₀ ^ ∑ S ∈ T, Molecule.ladderLength S := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun S hS => by rw [hX₀ S hS]
    have hC : (∏ S ∈ T, X S ^ Molecule.ladderLength S) * ∏ S ∈ A, X S ^ Molecule.ladderLength S ≤
        ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, X S ^ Molecule.ladderLength S := by
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
  · push_neg at hex
    have hMA : M.maximalLadders ⊆ A := fun S hS => by
      rw [hA, Finset.mem_filter]; exact ⟨hS, hex S hS⟩
    calc ∏ S ∈ M.maximalLadders, X S ^ Molecule.ladderLength S
        ≤ ∏ S ∈ (M.cut v v₂ x₁ x₂).maximalLadders, X S ^ Molecule.ladderLength S :=
          prod_mono_real (hMA.trans hAC) _ (fun S _ => hpos S)
      _ ≤ K ^ 2 * _ := by nlinarith

end WaveTurbulence.FinalCount
