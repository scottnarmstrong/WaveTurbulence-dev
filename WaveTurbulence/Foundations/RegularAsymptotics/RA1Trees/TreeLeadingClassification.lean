/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingChainJ
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeJBCutoff
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.NonspecialCoefficient
public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Special

/-! # The actual tree leading coefficient is the signed literal JBtree or zero -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set ClassJR Cancel MainCoef Links
open scoped Classical

/-- The literal source special-set test agrees with the recursive chain candidates at
any sign root, including the negative tree root. -/
theorem tree_isSpecialSet_at_root_iff (X : RegChain) (ζ : ℤˣ) (Z : Finset Cancel.Addr) :
    IsSpecialSet (X.linksAt ζ (rootT ζ)) Z ↔ ∀ z ∈ Z, z ∈ chainSpecial X ζ (rootT ζ) := by
  unfold IsSpecialSet
  exact forall₂_congr (fun z _ => (mem_chainSpecial_iff X ζ (rootT ζ) z).symm)

/-- Full source classification: non-dominant or non-special components vanish; otherwise
the actual component equals (-1)^|Z| times the original tree time factor (F61). -/
theorem treeRegularizedLeading_eq_if_special (X : RegChain) (ζ : ℤˣ) (Z : Finset Cancel.Addr)
    (hZ : Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)))
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    treeRegularizedLeading Z X ζ t s =
      if X.dominant = true ∧ IsSpecialSet (X.linksAt ζ (rootT ζ)) Z then
        (-1:ℂ)^Z.card*(X.JBtree 0 t s:ℂ) else 0 := by
  have hZ' : Z ⊆ WaveTurbulence.chosenSet (X.linksAt ζ (rootT ζ)) := by
    simpa only [linksAt_toJRc, ClassJR.chosenSet, WaveTurbulence.chosenSet] using hZ
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨hs.trans hst.le,ht⟩
  rw [treeRegularizedLeading_eq_chainJ Z X ζ hs hst ht]
  by_cases hd : X.dominant = true
  · by_cases hsp : IsSpecialSet (X.linksAt ζ (rootT ζ)) Z
    · rw [ite_eq_left ⟨hd,hsp⟩]
      have hp := (tree_isSpecialSet_at_root_iff X ζ Z).mp hsp
      have he := chainJ_eq_JBchain Z X ζ (rootT ζ) hd (tree_chosen_nodup_at_root X ζ)
        (fun z hz _ => hp z hz) t ht' 1 (fun u => if s < u then 1 else 0)
        (fun u => if s < u then 1 else 0) (fun u _ => by split_ifs <;> simp)
      rw [he,one_mul,Finset.inter_eq_left.mpr hZ',tree_JBchain_cutoff_eq_JBtree X hs hst]
    · rw [ite_eq_right (fun h => hsp h.2)]
      have hn : ¬ ∀ z ∈ Z, z ∈ chainSpecial X ζ (rootT ζ) :=
        fun h => hsp ((tree_isSpecialSet_at_root_iff X ζ Z).mpr h)
      push Not at hn
      obtain ⟨z,hz,hnz⟩ := hn
      exact chainJ_eq_zero_of_nonspecial Z z hz X ζ (rootT ζ) (hZ' hz) hnz t ht' _
  · rw [ite_eq_right (fun h => hd h.1)]
    exact chainJ_eq_zero Z X ζ (rootT ζ) (Bool.eq_false_iff.mpr hd) t ht' _

end WaveTurbulence.RegAsymp
