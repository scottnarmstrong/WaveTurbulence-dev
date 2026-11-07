/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg4Time
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg2Dec
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw6Pairs

/-! # V5 Step 4d-B: geometry of the upper block `S` at a twist at its LOWER joint

`STw P RS RS'`: the region data `RS`, `RS'` of the upper block `S` (joints `a`, `b = P.lower`) of a garden and of its
image `twistedAtoms S` under the unit twist `P`, with kept slot of the lower joint equal to the retained slot `P.keep`
(in both gardens: this is how a split at the member `p*` looks).  Then the retained leaf `r`, its partner and the lower
joint are internal to `S` (resp. their images to `S'`), and the realization nodes of `S` and `S'` correspond under the
naive node bijection (no rigidity: the exceptional leaves and lower joint are INTERIOR to `S`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (RS : CLRegionData G S a b)
  (RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b))

/-- The upper block `S` of a split at the twisted member: lower joint `b = P.lower`, kept slot the retained slot. -/
structure STw : Prop where
  block : G.molecule.IsBlock S a b
  lower : b = P.lower
  keep : RS.kept = P.keep
  keep' : RS'.kept = P.keep

variable {P RS RS'} (h : STw P RS RS')
include h

namespace STw

theorem lower_mem : P.lower ∈ S := h.lower ▸ h.block.2.2.1

theorem a_ne_lower : a ≠ P.lower := h.lower ▸ h.block.2.2.2.1

theorem placement : IsPlacementAt G S P.lower P := by
  obtain ⟨hb, hl, hk, hk'⟩ := h
  subst hl
  refine ⟨rfl, fun i => ?_⟩
  rw [RS.lower i, hk]

theorem placement' : IsPlacementAt (unitTwistGarden G P) (twistedAtoms G P S) (reversePlacement G P).lower
    (reversePlacement G P) := by
  obtain ⟨hb, hl, hk, hk'⟩ := h
  subst hl
  refine ⟨rfl, fun i => (RS'.lower i).trans ?_⟩
  rw [hk']
  rfl

theorem retained_internal : Mole.IsInternalLeaf G S P.retained := by
  have hpp := placement_paired_parent_mem G P (placement h)
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  refine ⟨P.unmarked, retained_nonroot G P, P.paired_nonroot, ?_, hpp⟩
  show G.molecule.atom (retainedLP G P) ∈ S
  rw [ha]; exact h.lower_mem

theorem partner_internal : Mole.IsInternalLeaf G S (G.pair P.retained) :=
  (Mole.internal_leaf_pair_iff G S P.retained).mpr h.retained_internal

theorem retained_internal' :
    Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) (eL P P.retained) := by
  have hpp := placement_paired_parent_mem (unitTwistGarden G P) (reversePlacement G P) (placement' h)
  have ha : (unitTwistGarden G P).molecule.atom (retainedLP (unitTwistGarden G P) (reversePlacement G P)) =
      (reversePlacement G P).lower := retained_parent _ (reversePlacement G P)
  refine ⟨(reversePlacement G P).unmarked, retained_nonroot _ (reversePlacement G P),
    (reversePlacement G P).paired_nonroot, ?_, hpp⟩
  show (unitTwistGarden G P).molecule.atom (retainedLP (unitTwistGarden G P) (reversePlacement G P)) ∈ _
  rw [ha]; exact (mem_twistedAtoms G P S P.lower).mpr h.lower_mem

theorem partner_internal' :
    Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) ((unitTwistGarden G P).pair (eL P P.retained)) :=
  (Mole.internal_leaf_pair_iff _ _ _).mpr h.retained_internal'

/-- The realization nodes of `S` and of `S'` correspond under the naive node bijection. -/
theorem real_iff (x : GNode G.tree) :
    Mole.InIncidenceRealization G S x ↔
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P x) := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective x
  cases q with
  | inl b =>
    change Mole.InIncidenceRealization G S b.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P b.toNode)
    have e1 := Mole.branch_incidence_realization_iff G S b
    have e2 := Mole.branch_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P b)
    have hn : naiveNodeEquiv G P b.toNode = (coreBranchEquiv G P b).toNode := naiveNodeEquiv_branch G P b
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P b.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P b).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) n) hn)
    exact e1.trans ((mem_twistedAtoms G P S b).symm.trans (e2.symm.trans e3.symm))
  | inr l =>
    change Mole.InIncidenceRealization G S l.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P l.toNode)
    have e1 := Mole.leaf_incidence_realization_iff G S l
    have e2 := Mole.leaf_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P l)
    have hn : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P l.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P l).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) n) hn)
    refine e1.trans (Iff.trans ?_ (e2.symm.trans e3.symm))
    by_cases hr1 : l = P.retained
    · subst hr1
      exact iff_of_true h.retained_internal h.retained_internal'
    by_cases hr2 : l = G.pair P.retained
    · subst hr2
      refine iff_of_true h.partner_internal ?_
      have := h.partner_internal'
      change Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
      rw [unitTwistGarden_pair] at this
      exact this
    · exact (ordinary_internal_iff G P l hr1 hr2).symm

theorem lower_real : P.lower.toNode ∈ clRealizationNodes G S :=
  (branch_mem_clRealizationNodes _).mpr h.lower_mem

theorem retained_real : P.retained.toNode ∈ clRealizationNodes G S :=
  (leaf_mem_clRealizationNodes _).mpr h.retained_internal

theorem partner_real : (G.pair P.retained).toNode ∈ clRealizationNodes G S :=
  (leaf_mem_clRealizationNodes _).mpr h.partner_internal

theorem excluded_eq : RS'.excluded = RS.excluded := by
  have hal : a ≠ P.lower := h.a_ne_lower
  have h1 : ¬ RS'.excluded.succ ∈ Mole.internalPositions (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P a) :=
    fun h => ((RS'.upper RS'.excluded).mp h) rfl
  have h2 : ¬ RS'.excluded.succ ∈ Mole.internalPositions G S a := fun h =>
    h1 ((internalPositions_twist_other G P S a hal _).mpr h)
  by_contra hne
  exact h2 ((RS.upper RS'.excluded).mpr hne)

theorem excl_child_ne_lower : a.child RS.excluded ≠ P.lower.toNode := by
  intro he
  have hr := (mem_real_iff h.block RS _).mp h.lower_real
  exact hr.2.1 (he ▸ isDesc_refl' _)

theorem excl_child_ne_partner : a.child RS.excluded ≠ (G.pair P.retained).toNode := by
  intro he
  have hr := (mem_real_iff h.block RS _).mp h.partner_real
  exact hr.2.1 (he ▸ isDesc_refl' _)

theorem naive_excl_child : naiveNodeEquiv G P (a.child RS.excluded) = (eB P a).child RS'.excluded := by
  have := naiveNodeEquiv_child G P (p := a) (n := a.child RS.excluded) (i := RS.excluded) rfl
    h.excl_child_ne_lower h.excl_child_ne_partner
  have hpa : a.1 ≠ P.lower.1 := fun he => h.a_ne_lower (Subtype.ext he)
  have e : exchangeChildSlot P.lower.1 P.keep a.1 RS.excluded = RS.excluded := by simp [exchangeChildSlot, hpa]
  rw [e] at this
  rw [h.excluded_eq]
  exact this

/-- The upper support of the two regions correspond under the naive bijection. -/
theorem splitA_iff (x : GNode G.tree) : x ∈ splitA RS ↔ naiveNodeEquiv G P x ∈ splitA RS' := by
  have h1 : naiveNodeEquiv G P a.toNode = (eB P a).toNode := naiveNodeEquiv_branch G P a
  unfold splitA
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, mem_clRealizationNodes]
  refine or_congr (h.real_iff x) ?_
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl h1
    · exact Or.inr h.naive_excl_child
  · rintro (hh | hh)
    · exact Or.inl ((naiveNodeEquiv G P).injective (hh.trans h1.symm))
    · exact Or.inr ((naiveNodeEquiv G P).injective (hh.trans h.naive_excl_child.symm))

end STw

end WaveTurbulence.VineEstS5B
