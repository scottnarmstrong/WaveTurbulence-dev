/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg1Geom

/-! # Rigid relocation of the upper block: the extended decorations (V5 Step 4b, step 4, WP-B part 2)

`extSEquiv`: `ExtS RS' L base β0 β1 ≃ ExtS RS L base β0 β1`, `x' ↦ x' ∘ naive` (no exchange of labels), for the upper block `S`
of a garden and its rigid image under a unit twist.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hS : G.molecule.IsBlock S a b) (hR : RigidAt P S b) (RS : CLRegionData G S a b)
  (RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b))

include hS hR in
theorem excluded_eq_rigid : RS'.excluded = RS.excluded := by
  have hal : a ≠ P.lower := hR.ne_lower hS.2.1
  have h1 : ¬ RS'.excluded.succ ∈ Mole.internalPositions (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P a) :=
    fun h => ((RS'.upper RS'.excluded).mp h) rfl
  have h2 : ¬ RS'.excluded.succ ∈ Mole.internalPositions G S a := fun h =>
    h1 ((internalPositions_twist_other G P S a hal _).mpr h)
  by_contra hne
  exact h2 ((RS.upper RS'.excluded).mpr hne)

include hS hR in
/-- The kept slot of the lower joint `b` of the upper block is unchanged. -/
theorem kept_eq_rigid : RS'.kept = RS.kept := by
  have hbl : b ≠ P.lower := hR.ne_lower hS.2.2.1
  have h1 := (RS.lower RS.kept).mpr rfl
  have h2 := (internalPositions_twist_other G P S b hbl RS.kept.succ).mpr h1
  exact ((RS'.lower RS.kept).mp h2).symm

include hS hR in
theorem splitA_iff (x : GNode G.tree) :
    x ∈ splitA RS ↔ naiveNodeEquiv G P x ∈ splitA RS' := by
  have hab : a ∈ S.erase b := Finset.mem_erase.mpr ⟨hS.2.2.2.1, hS.2.1⟩
  have hex := excluded_eq_rigid P hS hR RS RS'
  have h1 : naiveNodeEquiv G P a.toNode = (coreBranchEquiv G P a).toNode := naiveNodeEquiv_branch G P a
  have h2 : naiveNodeEquiv G P (a.child RS.excluded) = (coreBranchEquiv G P a).child RS'.excluded := by
    rw [hex]; exact hR.child_naive hab _
  unfold splitA
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, mem_clRealizationNodes]
  refine or_congr (RigidAt.real_iff P hR x) ?_
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl h1
    · exact Or.inr h2
  · rintro (h | h)
    · exact Or.inl ((naiveNodeEquiv G P).injective (h.trans h1.symm))
    · exact Or.inr ((naiveNodeEquiv G P).injective (h.trans h2.symm))

theorem mem_erase_twisted (v : GBranch G.tree) :
    eB P v ∈ (twistedAtoms G P S).erase (eB P b) ↔ v ∈ S.erase b := by
  rw [Finset.mem_erase, Finset.mem_erase, (eB P).injective.ne_iff]
  exact and_congr Iff.rfl (mem_twistedAtoms G P S v)

section Dec
variable {d : ℕ} (L : ℝ) (base : Mom d) (β0 β1 : Mom d)

include hR in
theorem consOn_rigid (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ)) :
    consOn ((twistedAtoms G P S).erase (eB P b)) x' ↔
      consOn (S.erase b) (fun y => x' (naiveNodeEquiv G P y)) := by
  constructor
  · intro h v hv
    have h1 := h (eB P v) ((mem_erase_twisted P v).mpr hv)
    have n0 : naiveNodeEquiv G P v.toNode = (coreBranchEquiv G P v).toNode := naiveNodeEquiv_branch G P v
    simp only [hR.child_naive hv, n0]
    exact h1
  · intro h v' hv'
    obtain ⟨v, rfl⟩ := (eB P).surjective v'
    have hv : v ∈ S.erase b := (mem_erase_twisted P v).mp hv'
    have h1 := h v hv
    have n0 : naiveNodeEquiv G P v.toNode = (coreBranchEquiv G P v).toNode := naiveNodeEquiv_branch G P v
    simp only [hR.child_naive hv, n0] at h1
    exact h1

include hR in
theorem leafOn_rigid (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ)) :
    leafOn (unitTwistGarden G P) (twistedAtoms G P S) x' ↔
      leafOn G S (fun y => x' (naiveNodeEquiv G P y)) := by
  have hr1 : ∀ l : GLeaf G.tree, Mole.IsInternalLeaf G S l → l ≠ P.retained ∧ l ≠ G.pair P.retained := by
    intro l hl
    exact ⟨fun h => not_internal_retained_of P hR.lower_notMem (h ▸ hl),
      fun h => not_internal_pair_of P hR.lower_notMem (h ▸ hl)⟩
  have hl' : (reversePlacement G P).lower ∉ twistedAtoms G P S := fun h =>
    hR.lower_notMem ((mem_twistedAtoms G P S P.lower).mp h)
  constructor
  · intro h l hl
    obtain ⟨h1, h2⟩ := hr1 l hl
    have hl2 := (ordinary_internal_iff G P l h1 h2).mpr hl
    have := h _ hl2
    have n0 : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
    have n1 : naiveNodeEquiv G P (G.pair l).toNode = (coreLeafEquiv G P (G.pair l)).toNode := naiveNodeEquiv_leaf G P _
    have hp : coreLeafEquiv G P (G.pair l) = (unitTwistGarden G P).pair (coreLeafEquiv G P l) :=
      (unitTwistGarden_pair G P l).symm
    change x' (naiveNodeEquiv G P l.toNode) = x' (naiveNodeEquiv G P (G.pair l).toNode)
    rw [n0, n1, hp]
    exact this
  · intro h l' hl'i
    obtain ⟨l, rfl⟩ := (coreLeafEquiv G P).surjective l'
    have h1 : l ≠ P.retained := fun e => by
      subst e
      have := not_internal_retained_of (reversePlacement G P) hl'
      exact this hl'i
    have h2 : l ≠ G.pair P.retained := fun e => by
      subst e
      have := not_internal_pair_of (reversePlacement G P) hl'
      change ¬ Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
      rw [unitTwistGarden_pair] at this
      exact this hl'i
    have hl2 := (ordinary_internal_iff G P l h1 h2).mp hl'i
    have := h l hl2
    have n0 : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
    have n1 : naiveNodeEquiv G P (G.pair l).toNode = (coreLeafEquiv G P (G.pair l)).toNode := naiveNodeEquiv_leaf G P _
    have hp : coreLeafEquiv G P (G.pair l) = (unitTwistGarden G P).pair (coreLeafEquiv G P l) :=
      (unitTwistGarden_pair G P l).symm
    change x' (naiveNodeEquiv G P l.toNode) = x' (naiveNodeEquiv G P (G.pair l).toNode) at this
    rw [n0, n1, hp] at this
    exact this

include hS hR in
theorem extS_iff (x' : GNode (unitTwistGarden G P).tree → (Fin d → ℤ)) :
    (FreeS RS' x' ∧ BdS RS' L base β0 β1 x') ↔
      (FreeS RS (fun y => x' (naiveNodeEquiv G P y)) ∧ BdS RS L base β0 β1 (fun y => x' (naiveNodeEquiv G P y))) := by
  have hex := excluded_eq_rigid P hS hR RS RS'
  have hab : a ∈ S.erase b := Finset.mem_erase.mpr ⟨hS.2.2.2.1, hS.2.1⟩
  have h1 : naiveNodeEquiv G P a.toNode = (eB P a).toNode := naiveNodeEquiv_branch G P a
  have h2 : naiveNodeEquiv G P (a.child RS.excluded) = (eB P a).child RS'.excluded := by
    rw [hex]; exact hR.child_naive hab _
  unfold FreeS BdS
  refine and_congr (and_congr ?_ (and_congr (consOn_rigid P hR x') (leafOn_rigid P hR x'))) ?_
  · constructor
    · intro h y hy
      exact h _ (fun hh => hy ((splitA_iff P hS hR RS RS' y).mpr hh))
    · intro h y' hy'
      obtain ⟨y, rfl⟩ := (naiveNodeEquiv G P).surjective y'
      exact h y (fun hh => hy' ((splitA_iff P hS hR RS RS' y).mp hh))
  · simp only []
    rw [h1, h2]

/-- **The extended decorations of the upper block correspond (no exchange of labels).** -/
@[expose] noncomputable def extSEquiv (hS : G.molecule.IsBlock S a b) (hR : RigidAt P S b) :
    ExtS RS' L base β0 β1 ≃ ExtS RS L base β0 β1 :=
  Equiv.subtypeEquiv ((naiveNodeEquiv G P).symm.arrowCongr (Equiv.refl (Fin d → ℤ)))
    (fun x' => extS_iff P hS hR RS RS' L base β0 β1 x')

end Dec

end WaveTurbulence.VineEstS4
