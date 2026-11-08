/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlSep.Sep
/-! # FL-SEP corollary: the flower of an unmarked spliced SG block exits through `u₁₁`

Supplement §9.2 marking paragraph, on main's `RedSplice`/`VineB` vocabulary (`CLBlock`, `regionOf`,
`clRealizationNodes`, `crownSet`).  The block `u` has upper joint `u₁ = u.upper`, boundary nodes
`u₁₁ = u.upper.child excluded`, `u₂₁ = u.lower.child positive`, `u₂₂ = u.lower.child negative`.
If the flower lies below `u₁` and is not in the realization (unmarked block), and the SG gap
`‖k_{u₂₁} - k_{u₂₂}‖ < ‖k_root‖/2` holds, then the flower lies below `u₁₁`, and the only stem node in the realization
is `u₁`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FlSep
open Finset WaveTurbulence TTree WaveTurbulence.VineB WaveTurbulence.RegRed WaveTurbulence.RedSplice

variable {w : ℕ}

/-- If the stem passes through a lower child of `b` (a stem node `b`), the other lower child is not stem. The two
crown children `u₂₁`, `u₂₂` cannot both lie on the stem, and a stem one forces a separated pair. -/
theorem crown_not_gap (LG : LayeredGarden w) (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)
    (hk : IsBranchConsistent k) (hG : LG.garden.IsFlowerGarden)
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    (b : GBranch LG.garden.tree) {i j : Fin 3} (hij : i ≠ j) (hi : LG.OnStem (b.child i))
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree b.1.1)‖ / 4) :
    ‖k (GNode.root LG.garden.tree b.1.1)‖ / 2 ≤ ‖k (b.child i) - k (b.child j)‖ := by
  have hbst : LG.OnStem b.toNode := by
    obtain ⟨ℓ, hℓ, hd⟩ := hi
    exact ⟨ℓ, hℓ, (GBranch.isDesc_child b i).trans hd⟩
  have hbl : LG.layer b.toNode = p := layer_eq_of_onStem LG p hlay hfl hbst
  have e : (b.child i).1.1 = b.1.1 := rfl
  have := separation LG p N r k hk hG hlay hfl hN hr0 hfr hi (isTopNode_child LG p hlay b hbl j)
    (not_onStem_sibling LG hG b hij hi) (by rw [e]; exact hK)
  rwa [e] at this

/-- **SG exit through `u₁₁`.** -/
theorem exit_through_u11 (LG : LayeredGarden w) (p N : ℕ) {d : ℕ} (r : ℝ) (k : GNode LG.garden.tree → Mom d)
    (hk : IsBranchConsistent k) (hG : LG.garden.IsFlowerGarden)
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, LG.IsFlowerNode a → ¬ LG.layer a < p)
    (hN : ∀ j, LG.topOrder p j ≤ N) (hr0 : 0 ≤ r)
    (hfr : ∀ a, LG.IsTopLeaf p a → ¬ LG.IsFlowerNode a → ‖k a‖ ≤ r)
    (u : CLBlock LG.garden)
    (hunm : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ → ℓ.toNode ∉ clRealizationNodes LG.garden u.atoms)
    (hup : LG.OnStem u.upper.toNode)
    (hK : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree u.upper.1.1)‖ / 4)
    (hgap : ‖k (u.lower.child (regionOf u).positive) - k (u.lower.child (regionOf u).negative)‖ <
      ‖k (GNode.root LG.garden.tree u.upper.1.1)‖ / 2) :
    LG.OnStem (u.upper.child (regionOf u).excluded) ∧
      ∀ x ∈ clRealizationNodes LG.garden u.atoms, LG.OnStem x → x = u.upper.toNode := by
  have hlow : u.upper.1.1 = u.lower.1.1 := (lower_desc u).1
  have hdis := (regionOf u).distinct
  have hK' : (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree u.lower.1.1)‖ / 4 := by
    rw [← hlow]; exact hK
  have hgap' : ‖k (GNode.root LG.garden.tree u.lower.1.1)‖ / 2 > ‖k (u.lower.child (regionOf u).positive) -
      k (u.lower.child (regionOf u).negative)‖ := by rw [← hlow]; exact hgap
  have h11 : LG.OnStem (u.upper.child (regionOf u).excluded) := by
    obtain ⟨ℓ, hℓ, hd⟩ := hup
    have hnr := hunm ℓ hℓ
    rw [real_iff] at hnr
    have hc : (u.upper.child (regionOf u).excluded).IsDesc ℓ.toNode ∨
        (u.lower.child (regionOf u).positive).IsDesc ℓ.toNode ∨
        (u.lower.child (regionOf u).negative).IsDesc ℓ.toNode := by
      by_contra hcon
      push Not at hcon
      exact hnr ⟨hd, hcon.1, hcon.2.1, hcon.2.2⟩
    rcases hc with h | h | h
    · exact ⟨ℓ, hℓ, h⟩
    · exfalso
      have := crown_not_gap LG p N r k hk hG hlay hfl hN hr0 hfr u.lower hdis ⟨ℓ, hℓ, h⟩ hK'
      linarith
    · exfalso
      have := crown_not_gap LG p N r k hk hG hlay hfl hN hr0 hfr u.lower (Ne.symm hdis) ⟨ℓ, hℓ, h⟩ hK'
      rw [norm_sub_rev] at this
      linarith
  refine ⟨h11, ?_⟩
  intro x hx hxs
  obtain ⟨hx1, hx2, -, -⟩ := (real_iff u x).mp hx
  obtain ⟨ℓ', hℓ', hdx⟩ := hxs
  obtain ⟨ℓ'', hℓ'', hd11⟩ := h11
  have htree : ℓ'.1.1 = ℓ''.1.1 := by
    have e1 : x.1.1 = ℓ'.toNode.1.1 := hdx.1
    have e2 : (u.upper.child (regionOf u).excluded).1.1 = ℓ''.toNode.1.1 := hd11.1
    have e3 : u.upper.toNode.1.1 = x.1.1 := hx1.1
    have e4 : (u.upper.child (regionOf u).excluded).1.1 = u.upper.toNode.1.1 := rfl
    exact (e1.symm.trans (e3.symm.trans (e4.symm.trans e2)))
  have := flower_unique LG hG htree hℓ' hℓ''
  subst this
  rcases le_total x.1.2.length (u.upper.child (regionOf u).excluded).1.2.length with hle | hle
  · have hpre : x.1.2 <+: (u.upper.child (regionOf u).excluded).1.2 :=
      List.prefix_of_prefix_length_le hdx.2 hd11.2 hle
    have hdesc : x.IsDesc (u.upper.child (regionOf u).excluded) := ⟨by
      have e3 : u.upper.toNode.1.1 = x.1.1 := hx1.1
      exact e3.symm.trans rfl, hpre⟩
    rcases (isDesc_child_iff u.upper (regionOf u).excluded).1 hdesc with h | h
    · exact absurd (h ▸ GNode.isDesc_refl x) hx2
    · exact isDesc_antisymm' h hx1
  · have hpre : (u.upper.child (regionOf u).excluded).1.2 <+: x.1.2 :=
      List.prefix_of_prefix_length_le hd11.2 hdx.2 hle
    exact absurd ⟨by
      have e3 : u.upper.toNode.1.1 = x.1.1 := hx1.1
      exact (rfl : (u.upper.child (regionOf u).excluded).1.1 = u.upper.toNode.1.1).trans e3, hpre⟩ hx2

end WaveTurbulence.Flower.FlSep
