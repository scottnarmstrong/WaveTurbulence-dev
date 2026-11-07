/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrCount
public import WaveTurbulence.Foundations.FinalCount.VrHyper1
import Mathlib.Tactic

/-! # VINE-RHO (7): the vine bound transported along an agreement `Agree M M' a b`

`vine_ladderLoss_le_of_agree`: if `S` is a vine of the molecule `M'` which agrees with `M` away from the joints, then
`ladderLoss M (M.atoms \ S) ≤ 42` (the loss is measured in `M`).  Also subadditivity of the loss under unions. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.Vine WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
open scoped Classical
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

theorem vine_ladderLoss_le_of_agree (M : Molecule V D) (hM : M.IsMolecule) (M' : Molecule V D') (hM' : M'.IsMolecule)
    {X : VineType} {S : Finset V} {a b p q : V} (hA : Agree M M' p q) (hV : M'.IsVine X S a b)
    (hp : p ∈ S → p = a ∨ p = b) (hq : q ∈ S → q = a ∨ q = b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨hB, ⟨R⟩⟩ := isVine_iff_realization.1 hV
  have hdeg : ∀ x ∈ M.atoms, M.deg x ≤ 4 := fun x hx => Mole.deg_le_four M hM hx
  have hdis := LadderDisjoint.maximalLadders_pairwiseDisjoint_of_degree_le_four M hdeg
  set Rep := tmplAtoms R ∪ firstAtoms R with hRep
  have hRepcard : Rep.card ≤ 21 := by
    rw [hRep]
    have := card_union_le (tmplAtoms R) (firstAtoms R)
    have := tmplAtoms_card R
    have := firstAtoms_card R
    omega
  have hcover : ∀ c ∈ S, c ∈ Rep ∨ ∃ N ∈ M.maximalLadders, c ∈ N ∧ ∃ r ∈ Rep, r ∈ N := by
    intro c hc
    by_cases hlow : R.f c < X.template.n
    · exact Or.inl (mem_union_left _ (mem_filter.2 ⟨hc, hlow⟩))
    · obtain ⟨A, i, h1, h2, hcA⟩ := R.fresh_slot hc (not_lt.1 hlow)
      have hu1 : A.Q.u 1 ∈ Rep := mem_union_right _ (mem_filter.2 ⟨(A.mem 1).1, A, by omega, Or.inl rfl⟩)
      by_cases hk : A.k = 1
      · left
        have hi : i = 1 := by omega
        subst hi
        rcases hcA with rfl | rfl
        · exact hu1
        · exact mem_union_right _ (mem_filter.2 ⟨(A.mem 1).2, A, by omega, Or.inr rfl⟩)
      · right
        obtain ⟨m, u, w, hL', hLmem, hnj0, hmS⟩ := slot_ladder_free M' hM' R hB A (by omega)
        have hnj : ∀ j, u j ≠ p ∧ u j ≠ q ∧ w j ≠ p ∧ w j ≠ q := by
          intro j
          obtain ⟨h1, h2, h3, h4⟩ := hnj0 j
          obtain ⟨s1, s2⟩ := hmS j
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
          · rcases hp (h ▸ s1) with h' | h' <;> simp_all
          · rcases hq (h ▸ s1) with h' | h' <;> simp_all
          · rcases hp (h ▸ s2) with h' | h' <;> simp_all
          · rcases hq (h ▸ s2) with h' | h' <;> simp_all
        have hL : M.IsLadderSet (Molecule.ladderAtoms u w) := ⟨m, u, w, ladder_of_agree hA hL' hnj, rfl⟩
        obtain ⟨N₀, hN₀, hLN⟩ := exists_maximal_ladder_ge M hL
        have hcL : c ∈ Molecule.ladderAtoms u w := by
          rcases hcA with rfl | rfl
          · exact (hLmem i h1 h2).1
          · exact (hLmem i h1 h2).2
        exact ⟨N₀, hN₀, hLN hcL, A.Q.u 1, hu1, hLN (hLmem 1 le_rfl (by omega)).1⟩
  unfold ladderLoss
  have hA' : (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ S).card ≤ Rep.card := by
    have hex : ∀ N ∈ M.maximalLadders.filter (fun N => ¬ N ⊆ M.atoms \ S), ∃ r ∈ Rep, r ∈ N := by
      intro N hN
      rw [mem_filter] at hN
      obtain ⟨hNm, hNS⟩ := hN
      have hNatoms := isLadderSet_subset M ((mem_maximalLadders_iff M).1 hNm).1
      obtain ⟨c, hcN, hcS⟩ := Finset.not_subset.1 hNS
      have hcS' : c ∈ S := by
        by_contra h
        exact hcS (mem_sdiff.2 ⟨hNatoms hcN, h⟩)
      rcases hcover c hcS' with h | ⟨N₀, hN₀, hcN₀, r, hr, hrN₀⟩
      · exact ⟨c, h, hcN⟩
      · have hNN : N = N₀ := by
          by_contra hne
          exact Finset.disjoint_left.1 (hdis hNm hN₀ hne) hcN hcN₀
        exact ⟨r, hr, hNN ▸ hrN₀⟩
    have : Nonempty V := ⟨a⟩
    choose! r hr using hex
    refine card_le_card_of_injOn r (fun N hN => (hr N hN).1) ?_
    intro N hN N' hN' e
    have hN1 := (mem_filter.1 hN).1
    have hN1' := (mem_filter.1 hN').1
    by_contra hne
    exact Finset.disjoint_left.1 (hdis hN1 hN1' hne) (hr N hN).2 (e ▸ (hr N' hN').2)
  have hF : (M.atoms.filter fun v => v ∉ M.atoms \ S ∧ ∀ N ∈ M.maximalLadders, v ∉ N).card ≤ Rep.card := by
    apply card_le_card
    intro v hv
    rw [mem_filter] at hv
    have hvS : v ∈ S := by
      by_contra h
      exact hv.2.1 (mem_sdiff.2 ⟨hv.1, h⟩)
    rcases hcover v hvS with h | ⟨N₀, hN₀, hvN₀, _⟩
    · exact h
    · exact absurd hvN₀ (hv.2.2 N₀ hN₀)
  omega

/-- The loss is subadditive: removing `S ∪ T` costs at most the sum of removing `S` and removing `T`. -/
theorem ladderLoss_union_le (M : Molecule V D) (S T : Finset V) :
    ladderLoss M (M.atoms \ (S ∪ T)) ≤ ladderLoss M (M.atoms \ S) + ladderLoss M (M.atoms \ T) := by
  unfold ladderLoss
  have h1 : (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ (S ∪ T)) ⊆
      (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ S) ∪ (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ T) := by
    intro N hN
    simp only [mem_filter, mem_union] at hN ⊢
    obtain ⟨hm, hn⟩ := hN
    have hNa := isLadderSet_subset M ((mem_maximalLadders_iff M).1 hm).1
    obtain ⟨c, hcN, hc⟩ := Finset.not_subset.1 hn
    have hcST : c ∈ S ∪ T := by
      by_contra h; exact hc (mem_sdiff.2 ⟨hNa hcN, h⟩)
    rcases mem_union.1 hcST with h | h
    · left; refine ⟨hm, fun hsub => ?_⟩
      exact (mem_sdiff.1 (hsub hcN)).2 h
    · right; refine ⟨hm, fun hsub => ?_⟩
      exact (mem_sdiff.1 (hsub hcN)).2 h
  have h2 : (M.atoms.filter fun v => v ∉ M.atoms \ (S ∪ T) ∧ ∀ N ∈ M.maximalLadders, v ∉ N) ⊆
      (M.atoms.filter fun v => v ∉ M.atoms \ S ∧ ∀ N ∈ M.maximalLadders, v ∉ N) ∪
      (M.atoms.filter fun v => v ∉ M.atoms \ T ∧ ∀ N ∈ M.maximalLadders, v ∉ N) := by
    intro v hv
    simp only [mem_filter, mem_union, mem_sdiff, not_and, not_not] at hv ⊢
    obtain ⟨hva, hvn, hf⟩ := hv
    rcases hvn hva with h | h
    · left; exact ⟨hva, fun _ => h, hf⟩
    · right; exact ⟨hva, fun _ => h, hf⟩
  have := card_le_card h1
  have := card_union_le (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ S) (M.maximalLadders.filter fun N => ¬ N ⊆ M.atoms \ T)
  have := card_le_card h2
  have := card_union_le (M.atoms.filter fun v => v ∉ M.atoms \ S ∧ ∀ N ∈ M.maximalLadders, v ∉ N)
    (M.atoms.filter fun v => v ∉ M.atoms \ T ∧ ∀ N ∈ M.maximalLadders, v ∉ N)
  omega

end WaveTurbulence.VineRho
