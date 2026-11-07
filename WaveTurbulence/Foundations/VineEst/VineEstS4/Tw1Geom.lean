/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderCore
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel

/-! # K^T twist invariance, geometry (V5 Step 4b, step 3, part 1)

For a unit twist `(G, P)` and a CL block `T` whose UPPER joint is the lower joint `P.lower` of the placement, the block lies
below `P.lower`, so it avoids the two exceptional leaves (`retained`, `pair retained`) except through `P.lower` itself:
* `excluded_eq_keep`: the excluded child of the upper joint is the retained slot;
* `child_avoid`: no child of a branch of `T` other than `P.lower` is `P.lower`, `retained` or the partner of `retained`;
* `real_iff`: the realization nodes of `T` and of `twistedAtoms T` correspond under `naiveNodeEquiv`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}

theorem retainedLP_not_inGroup (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z) :
    ¬ G.molecule.InGroup T (retainedLP G P) := by
  intro hg
  have h2 : GNode.parent (G.pair P.retained).toNode P.paired_nonroot ∈ T := hg.2
  exact paired_parent_outside G P (Mole.block_one_root_descendants G hB hCL.1 hCL.2 h2)

theorem keep_not_internal (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z) :
    P.keep.succ ∉ Mole.internalPositions G T P.lower := by
  intro hi
  obtain ⟨x, ha, hg, hpos⟩ := (Mole.mem_internalPositions G).mp hi
  have he : x = retainedLP G P := Mole.atom_position_injective G
    (Prod.ext (ha.trans (retained_parent G P).symm) (hpos.trans (retainedLP_position G P).symm))
  subst x
  exact retainedLP_not_inGroup P hB hCL hg

/-- The excluded child of the upper joint `P.lower` of a block is the retained slot. -/
theorem excluded_eq_keep (hB : G.molecule.IsBlock T P.lower z) (R : CLRegionData G T P.lower z) :
    R.excluded = P.keep := by
  by_contra h
  exact keep_not_internal P hB R.parentPattern ((R.upper P.keep).mpr (Ne.symm h))

theorem desc_child {a v : GNode G.tree} (h : a.IsDesc v) (b : GBranch G.tree) (hb : b.toNode = v) (i : Fin 3) :
    a.IsDesc (b.child i) := by
  subst hb
  exact ⟨h.1, h.2.trans (List.prefix_append _ _)⟩

/-- No child of a branch of `T` other than `P.lower` is `P.lower`, `P.retained` or the partner of `P.retained`. -/
theorem child_avoid (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    {v : GBranch G.tree} (hv : v ∈ T) (hne : v ≠ P.lower) (i : Fin 3) :
    v.child i ≠ P.lower.toNode ∧ v.child i ≠ P.retained.toNode ∧ v.child i ≠ (G.pair P.retained).toNode := by
  have hd := Mole.block_one_root_descendants G hB hCL.1 hCL.2 hv
  have hdc := desc_child hd v rfl i
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hh := congrArg (fun n : GNode G.tree => n.1.2.length) he
    have hl := hd.2.length_le
    dsimp [GBranch.child, GBranch.toNode] at hh hl
    simp only [List.length_append, List.length_singleton] at hh
    omega
  · intro he
    exact hne ((Twist.parent_eq_of_child (n := P.retained.toNode) (retained_nonroot G P)
      (p := v) (i := i) he.symm).symm.trans (retained_parent G P))
  · intro he
    exact P.paired_outside (he ▸ hdc)

theorem not_internal_retained (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z) :
    ¬ Mole.IsInternalLeaf G T P.retained := by
  rintro ⟨hm, hn, hp, hg⟩
  exact retainedLP_not_inGroup P hB hCL hg

theorem not_internal_pair (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z) :
    ¬ Mole.IsInternalLeaf G T (G.pair P.retained) := fun h =>
  not_internal_retained P hB hCL ((Mole.internal_leaf_pair_iff G T P.retained).mp h)

/-- The realization nodes of `T` and of the twisted block correspond under the naive node bijection. -/
theorem real_iff (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    (hCL' : Mole.CLParentPattern (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P z)) (x : GNode G.tree) :
    Mole.InIncidenceRealization G T x ↔
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (naiveNodeEquiv G P x) := by
  have hB' := isBlock_twistedAtoms G P hB
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective x
  cases q with
  | inl b =>
    change Mole.InIncidenceRealization G T b.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P b.toNode)
    have e1 := Mole.branch_incidence_realization_iff G T b
    have e2 := Mole.branch_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P b)
    have hn : naiveNodeEquiv G P b.toNode = (coreBranchEquiv G P b).toNode := naiveNodeEquiv_branch G P b
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (naiveNodeEquiv G P b.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P b).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) n) hn)
    exact e1.trans ((mem_twistedAtoms G P T b).symm.trans (e2.symm.trans e3.symm))
  | inr l =>
    change Mole.InIncidenceRealization G T l.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P l.toNode)
    have e1 := Mole.leaf_incidence_realization_iff G T l
    have e2 := Mole.leaf_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P T) (coreLeafEquiv G P l)
    have hn : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (naiveNodeEquiv G P l.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (coreLeafEquiv G P l).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) n) hn)
    refine e1.trans (Iff.trans ?_ (e2.symm.trans e3.symm))
    by_cases h1 : l = P.retained
    · subst h1
      exact iff_of_false (not_internal_retained P hB hCL)
        (not_internal_retained (reversePlacement G P) hB' hCL')
    by_cases h2 : l = G.pair P.retained
    · subst h2
      refine iff_of_false (not_internal_pair P hB hCL) ?_
      have := not_internal_pair (reversePlacement G P) hB' hCL'
      change ¬ Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
      rw [unitTwistGarden_pair] at this
      exact this
    · exact (ordinary_internal_iff G P l h1 h2).symm

/-- The sign of an ordinary node is unchanged by the naive node bijection. -/
theorem sign_naive_ordinary (n : GNode G.tree) (h1 : n ≠ P.lower.toNode) (h2 : n ≠ P.retained.toNode)
    (h3 : n ≠ (G.pair P.retained).toNode) :
    (unitTwistGarden G P).sign (naiveNodeEquiv G P n) = G.sign n := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective n
  cases q with
  | inl b =>
    change (unitTwistGarden G P).sign (naiveNodeEquiv G P b.toNode) = G.sign b.toNode
    rw [naiveNodeEquiv_branch]
    have hb : b ≠ P.lower := fun h => h1 (congrArg GBranch.toNode h)
    rw [coreBranchEquiv_sign, ite_eq_right hb]
  | inr l =>
    change (unitTwistGarden G P).sign (naiveNodeEquiv G P l.toNode) = G.sign l.toNode
    rw [naiveNodeEquiv_leaf]
    have hr : l ≠ P.retained := fun h => h2 (congrArg GLeaf.toNode h)
    have hp : l ≠ G.pair P.retained := fun h => h3 (congrArg GLeaf.toNode h)
    have := coreLeafEquiv_sign G P l
    simp only [coreLeafMultiplier, hr, hp, or_self, ite_false, one_mul] at this
    exact this

theorem child_naive (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    {v : GBranch G.tree} (hv : v ∈ T) (hne : v ≠ P.lower) (i : Fin 3) :
    naiveNodeEquiv G P (v.child i) = (coreBranchEquiv G P v).child i := by
  obtain ⟨h1, h2, h3⟩ := child_avoid P hB hCL hv hne i
  have hpv : v.1 ≠ P.lower.1 := fun he => hne (Subtype.ext he)
  have := naiveNodeEquiv_child G P (p := v) (n := v.child i) (i := i) rfl h1 h3
  simpa only [exchangeChildSlot, hpv, ite_false] using this

/-- The slots of the transported region data of the lower block coincide with those of the original. -/
theorem region_eq (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    (R : CLRegionData G T P.lower z)
    (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P z)) :
    R'.excluded = R.excluded ∧ R'.kept = R.kept ∧ R'.positive = R.positive ∧ R'.negative = R.negative := by
  have hB' := isBlock_twistedAtoms G P hB
  have hex : R'.excluded = P.keep := excluded_eq_keep (reversePlacement G P) hB' R'
  have hzl : z ≠ P.lower := by
    intro h
    have := (Mole.cl_parent_strict_descendant G hB hCL).2
    rw [h] at this
    exact lt_irrefl _ this
  have hkp : R'.kept = R.kept := by
    have h1 := (R.lower R.kept).mpr rfl
    have h2 := (internalPositions_twist_other G P T z hzl R.kept.succ).mpr h1
    exact (R'.lower R.kept).mp h2 |>.symm
  have hne_pos : R.positive ≠ R.kept := fun h => by
    have := (R.lower_excluded R.positive).mpr (Or.inl rfl)
    exact this h
  have hne_neg : R.negative ≠ R.kept := fun h => by
    have := (R.lower_excluded R.negative).mpr (Or.inr rfl)
    exact this h
  have hsgn : ∀ i : Fin 3, (unitTwistGarden G P).sign ((coreBranchEquiv G P z).child i) = G.sign (z.child i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := child_avoid P hB hCL (Mole.cl_parent_strict_descendant G hB hCL |> fun _ => hB.2.2.1) hzl i
    rw [← child_naive P hB hCL hB.2.2.1 hzl i]
    exact sign_naive_ordinary P _ h1 h2 h3
  have hpos : R'.positive = R.positive := by
    have hp' : R'.positive ≠ R.kept := hkp ▸ (fun h => (R'.lower_excluded R'.positive |>.mpr (Or.inl rfl)) h)
    rcases (R.lower_excluded R'.positive).mp hp' with h | h
    · exact h
    · exfalso
      have h4 : G.sign (z.child R'.positive) = 1 := (hsgn _).symm.trans R'.positive_sign
      rw [h] at h4
      have := R.negative_sign
      rw [h4] at this
      exact absurd this (by decide)
  have hneg : R'.negative = R.negative := by
    have hp' : R'.negative ≠ R.kept := hkp ▸ (fun h => (R'.lower_excluded R'.negative |>.mpr (Or.inr rfl)) h)
    rcases (R.lower_excluded R'.negative).mp hp' with h | h
    · exfalso
      exact R'.distinct (hpos.trans h.symm)
    · exact h
  exact ⟨hex.trans (excluded_eq_keep P hB R).symm, hkp, hpos, hneg⟩

theorem mem_clLocalSupport {a b : GBranch G.tree} {U : Finset (GBranch G.tree)} (R : CLRegionData G U a b)
    (x : GNode G.tree) :
    x ∈ clLocalSupport R ↔ Mole.InIncidenceRealization G U x ∨ ∃ j, clBoundaryNodes R j = x := by
  classical
  simp only [clLocalSupport, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    clRealizationNodes, Finset.mem_filter]

/-- The four boundary nodes correspond under the naive node bijection. -/
theorem bd_naive (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    (R : CLRegionData G T P.lower z)
    (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P z)) (j : Fin 4) :
    naiveNodeEquiv G P (clBoundaryNodes R j) = clBoundaryNodes R' j := by
  obtain ⟨he, hk, hp, hn⟩ := region_eq P hB hCL R R'
  have hzl : z ≠ P.lower := by
    intro h
    have := (Mole.cl_parent_strict_descendant G hB hCL).2
    rw [h] at this
    exact lt_irrefl _ this
  have hex : R.excluded = P.keep := excluded_eq_keep P hB R
  fin_cases j
  · exact naiveNodeEquiv_branch G P P.lower
  · change naiveNodeEquiv G P (P.lower.child R.excluded) = (coreBranchEquiv G P P.lower).child R'.excluded
    rw [he, hex]
    have h1 : naiveNodeEquiv G P (P.lower.child P.keep) = naiveNodeEquiv G P P.retained.toNode :=
      congrArg _ P.child.symm
    refine h1.trans ((naiveNodeEquiv_leaf G P P.retained).trans ?_)
    exact (reversePlacement G P).child
  · change naiveNodeEquiv G P (z.child R.positive) = (coreBranchEquiv G P z).child R'.positive
    rw [hp]
    exact child_naive P hB hCL hB.2.2.1 hzl _
  · change naiveNodeEquiv G P (z.child R.negative) = (coreBranchEquiv G P z).child R'.negative
    rw [hn]
    exact child_naive P hB hCL hB.2.2.1 hzl _

/-- The node transposition `lower ↔ retained` composed with the naive node bijection. -/
@[expose] noncomputable def twNode : GNode G.tree ≃ GNode (unitTwistGarden G P).tree :=
  (Equiv.swap P.lower.toNode P.retained.toNode).trans (naiveNodeEquiv G P)

theorem twNode_apply (x : GNode G.tree) :
    twNode P x = naiveNodeEquiv G P (Equiv.swap P.lower.toNode P.retained.toNode x) := rfl

/-- The support of the region of the lower block corresponds under `twNode`. -/
theorem support_iff (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
    (R : CLRegionData G T P.lower z)
    (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P T) (coreBranchEquiv G P P.lower)
      (coreBranchEquiv G P z)) (x : GNode G.tree) :
    x ∈ clLocalSupport R ↔ twNode P x ∈ clLocalSupport R' := by
  have hB' := isBlock_twistedAtoms G P hB
  have hCL' := R'.parentPattern
  have key : ∀ y : GNode G.tree, y ∈ clLocalSupport R ↔ naiveNodeEquiv G P y ∈ clLocalSupport R' := by
    intro y
    refine (mem_clLocalSupport R y).trans (Iff.trans ?_ (mem_clLocalSupport R' (naiveNodeEquiv G P y)).symm)
    refine or_congr (real_iff P hB hCL hCL' y) ?_
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, (bd_naive P hB hCL R R' j).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, (naiveNodeEquiv G P).injective ((bd_naive P hB hCL R R' j).trans hj)⟩
  have hsw : ∀ y : GNode G.tree, y ∈ clLocalSupport R ↔ Equiv.swap P.lower.toNode P.retained.toNode y ∈ clLocalSupport R := by
    intro y
    have hl : P.lower.toNode ∈ clLocalSupport R := (mem_clLocalSupport R _).mpr (Or.inr ⟨0, rfl⟩)
    have hr : P.retained.toNode ∈ clLocalSupport R := (mem_clLocalSupport R _).mpr (Or.inr ⟨1, by
      have hex : R.excluded = P.keep := excluded_eq_keep P hB R
      change P.lower.child R.excluded = _
      rw [hex]; exact P.child.symm⟩)
    by_cases h1 : y = P.lower.toNode
    · subst h1; rw [Equiv.swap_apply_left]; exact ⟨fun _ => hr, fun _ => hl⟩
    by_cases h2 : y = P.retained.toNode
    · subst h2; rw [Equiv.swap_apply_right]; exact ⟨fun _ => hl, fun _ => hr⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  rw [hsw x]
  exact key _

end WaveTurbulence.VineEstS4
