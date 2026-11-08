/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.B.WeightN

/-! # V5W-B-WORLD B4: transport of the masked, normalized bond weight along family operations

* `exc_src`, `exc_out`: the exceptional tree and couple of an operation are coherent (incoherency `0`) in the source
  (from `htc`, `hcc` and canonicity, `ZpSurj.nativeCoh_of_cohOn`) and in the output (`ZpSurj.nativeCoh_op`).
* `ΨX_true`, `ΨX_false`: the dart weight is transported by the dart bijection of the operation, for every dart (off the
  exceptional incidences the rows are ordinary and keep incoherency and order; at the exceptional incidences both
  sides are coherent and carry the bond factor).
* `bWN_false`, `bWN_rigid`, `bWN_twist`, `bWN_twNode`: the four transports of V5-SPACE-EXT's `bW_*` for `bWN` (the
  label parts are V5-SPACE-EXT's, `VineSpaceB/Bond.lean`, re-proved verbatim).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS4 VineEstS5B Links
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts inGroup_mate_iff layX layX_true layX_false
  twistDartEquiv_eq_naive dartNode_naive atom_retainedLP)
open WaveTurbulence.Flower.V5W (nodeRowIncoh nodeRowIncoh_branch nodeRowIncoh_leaf coupleIncoh treeIncoh
  treeIncoh_LF coupleIncoh_LF tp_pairOfLeaf pairOfLeaf_ne_exceptional)

variable {w d : ℕ} {ι : Type*}

section Exc
variable {G : Garden w} (P : CorePlacement G)

/-- The four exceptional incidences of a unit twist (the lower PC bond and the retained LP bond). -/
def IsExc (y : GardenDart G) : Prop :=
  (∃ s, y = lowerPC G P s) ∨ y = retainedLP G P ∨ y = G.molecule.mate (retainedLP G P)

theorem twist_eq_naive_of_not_exc {y : GardenDart G} (hy : ¬ IsExc P y) :
    twistDartEquiv G P y = naiveDartEquiv G P y :=
  twistDartEquiv_eq_naive P y (fun s h => hy (Or.inl ⟨s, h⟩)) (fun h => hy (Or.inr (Or.inl h)))
    (fun h => hy (Or.inr (Or.inr h)))

theorem swap_of_not_exc {y : GardenDart G} (hy : ¬ IsExc P y) : exceptionalDartSwap G P y = y :=
  (naiveDartEquiv G P).injective (twist_eq_naive_of_not_exc P hy)

theorem swap_exc {y : GardenDart G} (hy : IsExc P y) : IsExc P (exceptionalDartSwap G P y) := by
  by_contra h
  have h1 := swap_of_not_exc P h
  have h2 : exceptionalDartSwap G P y = y := (exceptionalDartSwap G P).injective h1
  exact h (by rw [h2]; exact hy)

theorem exc_node {y : GardenDart G} (hy : IsExc P y) :
    Mole.dartNode G y = P.lower.toNode ∨ Mole.dartNode G y = P.retained.toNode ∨
      Mole.dartNode G y = (G.pair P.retained).toNode := by
  rcases hy with ⟨s, rfl⟩ | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- Off the exceptional incidences the carried node is ordinary. -/
theorem not_exc_cases {y : GardenDart G} (hy : ¬ IsExc P y) :
    (∃ (c : {c : GBranch G.tree // c.1.2 ≠ []}) (s : Bool), y = .inl (c, s) ∧ c.1 ≠ P.lower) ∨
    (∃ l : {l : GLeaf G.tree // G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ []},
      y = .inr l ∧ l.1 ≠ P.retained ∧ l.1 ≠ G.pair P.retained) := by
  rcases y with ⟨c, s⟩ | l
  · refine Or.inl ⟨c, s, rfl, fun hc => hy (Or.inl ⟨s, ?_⟩)⟩
    have he : c = ⟨P.lower, P.nonroot⟩ := Subtype.ext hc
    subst he
    rfl
  · refine Or.inr ⟨l, rfl, fun hl => hy (Or.inr (Or.inl ?_)), fun hp => hy (Or.inr (Or.inr ?_))⟩
    · have he : l = ⟨P.retained, P.unmarked, retained_nonroot G P, P.paired_nonroot⟩ := Subtype.ext hl
      subst he
      rfl
    · change Sum.inr l = Sum.inr _
      exact congrArg Sum.inr (Subtype.ext hp)

end Exc

/-- Two dart weights agree when the rows at their nodes have the same incoherency and (if incoherent) order. -/
theorem ΨX_eq_of {ι' : Type*} (W : WD d) (X : FamilyReconstruction w ι) (Y : FamilyReconstruction w ι')
    (y : GardenDart X.skeleton) (y' : GardenDart Y.skeleton)
    (h1 : nodeRowIncoh Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y) (Mole.dartNode Y.skeleton y') =
      nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y))
    (h2 : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) ≠ 0 →
      nodeRowExp Y.data Y.plain (stateLayer Y) (stateLayer_isLayering Y) (Mole.dartNode Y.skeleton y') =
        nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y)) :
    ΨX W Y y' = ΨX W X y := by
  unfold ΨX
  rw [h1]
  split_ifs with h
  · rfl
  · rw [h2 h]

section Op
variable {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))

include hcan htc hcc in
/-- **The exceptional rows of the source are coherent.** -/
theorem exc_src :
    treeIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) (A.family.placement i).lower = 0 ∧
      coupleIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A)
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) = 0 := by
  have hC : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (coupleRoot A.data A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) 0)
      (coupleRoot A.data A.plain (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) 1)) := by
    unfold coupleRoot
    simpa using hcc
  obtain ⟨h1, h2⟩ := ZpSurj.nativeCoh_of_cohOn A i (canonGC_of_canonicalObject hcan) hC htc
  exact ⟨VineEst.incoherency_eq_zero_of_isCoherentTreeAt h2, VineEst.incoherency_eq_zero_of_isCoherentCoupleAt h1⟩

/-- **The exceptional rows of the output are coherent.** -/
theorem exc_out {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε) :
    treeIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.placement i).lower) = 0 ∧
      coupleIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε
          (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)) = 0 := by
  obtain ⟨h1, h2⟩ := ZpSurj.nativeCoh_op A i hcan hel htc hcc con
  have t1 : treeIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      ((opOut A i hcan hel htc hcc con).family.placement i).lower = 0 :=
    VineEst.incoherency_eq_zero_of_isCoherentTreeAt h2
  have t2 : coupleIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (pairOfLeaf (opOut A i hcan hel htc hcc con).skeleton (opOut A i hcan hel htc hcc con).plain
        ((opOut A i hcan hel htc hcc con).family.placement i).retained) = 0 :=
    VineEst.incoherency_eq_zero_of_isCoherentCoupleAt h1
  rw [ZpSurj.op_lower_eq A i hcan hel htc hcc con] at t1
  rw [ZpSurj.op_pair_eq A i hcan hel htc hcc con] at t2
  exact ⟨t1, t2⟩

include hcan htc hcc in
/-- The rows at the nodes of the exceptional incidences of the source are coherent. -/
theorem nodeRowIncoh_exc_src {y : GardenDart A.skeleton} (hy : IsExc (A.family.placement i) y) :
    nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) (Mole.dartNode A.skeleton y) = 0 := by
  obtain ⟨e1, e2⟩ := exc_src A i hcan htc hcc
  rcases exc_node (A.family.placement i) hy with h | h | h <;> rw [h]
  · rw [nodeRowIncoh_branch]; exact e1
  · rw [nodeRowIncoh_leaf]; exact e2
  · rw [nodeRowIncoh_leaf, pairOfLeaf_partner]; exact e2

/-- The rows at the nodes of the images of the exceptional incidences in a TRUE output are coherent. -/
theorem nodeRowIncoh_exc_true (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {y : GardenDart A.skeleton} (hy : IsExc (A.family.placement i) y) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (Mole.dartNode (unitTwistGarden A.skeleton (A.family.placement i))
        (twistDartEquiv A.skeleton (A.family.placement i) y)) = 0 := by
  obtain ⟨e1, e2⟩ := exc_out A i hcan hel htc hcc con
  have hz := swap_exc (A.family.placement i) hy
  change nodeRowIncoh _ _ _ _ (Mole.dartNode (unitTwistGarden A.skeleton (A.family.placement i))
    (naiveDartEquiv A.skeleton (A.family.placement i) (exceptionalDartSwap A.skeleton (A.family.placement i) y))) = 0
  rw [dartNode_naive]
  rcases exc_node (A.family.placement i) hz with h | h | h <;> rw [h]
  · rw [naiveNodeEquiv_branch]
    exact (nodeRowIncoh_branch _ _ _ _ _).trans e1
  · rw [naiveNodeEquiv_leaf]
    refine (nodeRowIncoh_leaf _ _ _ _ _).trans ?_
    rw [← tp_pairOfLeaf]
    exact e2
  · rw [naiveNodeEquiv_leaf]
    refine (nodeRowIncoh_leaf _ _ _ _ _).trans ?_
    rw [← tp_pairOfLeaf, pairOfLeaf_partner]
    exact e2

/-- Ordinary branch rows along a TRUE operation keep incoherency and order. -/
theorem nodeDat_branch_true (con : LFConstruction (A.source i hcan hel htc hcc) true) (c : GBranch A.skeleton.tree)
    (hc : c ≠ (A.family.placement i).lower) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (coreBranchEquiv A.skeleton (A.family.placement i) c).toNode =
      nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.toNode ∧
    nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (coreBranchEquiv A.skeleton (A.family.placement i) c).toNode =
      nodeRowExp A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.toNode := by
  refine ⟨(nodeRowIncoh_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) (coreBranchEquiv A.skeleton (A.family.placement i) c)).trans
    ((treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) c hc).trans (nodeRowIncoh_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c).symm), ?_⟩
  exact (nodeRowExp_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) (coreBranchEquiv A.skeleton (A.family.placement i) c)).trans
    ((congrArg (fun LG : LayeredGarden 1 => 2 * LG.garden.order + 1) (native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) c hc)).trans
      (nodeRowExp_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c).symm)

/-- Ordinary branch rows along a FALSE operation keep incoherency and order. -/
theorem nodeDat_branch_false (con : LFConstruction (A.source i hcan hel htc hcc) false) (c : GBranch A.skeleton.tree)
    (hc : c ≠ (A.family.placement i).lower) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        c.toNode = nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.toNode ∧
    nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        c.toNode = nodeRowExp A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.toNode := by
  refine ⟨(nodeRowIncoh_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) c).trans
    ((treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) c hc).trans (nodeRowIncoh_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c).symm), ?_⟩
  exact (nodeRowExp_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) c).trans
    ((congrArg (fun LG : LayeredGarden 1 => 2 * LG.garden.order + 1) (native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) c hc)).trans
      (nodeRowExp_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c).symm)

/-- Ordinary leaf rows along a TRUE operation keep incoherency and order. -/
theorem nodeDat_leaf_true (con : LFConstruction (A.source i hcan hel htc hcc) true) (l : GLeaf A.skeleton.tree)
    (hl : l ≠ (A.family.placement i).retained) (hp : l ≠ A.skeleton.pair (A.family.placement i).retained) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (coreLeafEquiv A.skeleton (A.family.placement i) l).toNode =
      nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.toNode ∧
    nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (coreLeafEquiv A.skeleton (A.family.placement i) l).toNode =
      nodeRowExp A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.toNode := by
  have hne := pairOfLeaf_ne_exceptional A i hcan hel htc hcc l hl hp
  have e := tp_pairOfLeaf (A.family.placement i) A.plain l
  refine ⟨(nodeRowIncoh_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) (coreLeafEquiv A.skeleton (A.family.placement i) l)).trans
    (((congrArg (coupleIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) e.symm).trans
      (coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) _ hne)).trans (nodeRowIncoh_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l).symm), ?_⟩
  exact (nodeRowExp_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) (coreLeafEquiv A.skeleton (A.family.placement i) l)).trans
    (((congrArg (fun q => 2 * (nativeCoupleLayered (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) q).garden.order + 2) e.symm).trans
      (congrArg (fun LG : LayeredGarden 2 => 2 * LG.garden.order + 2) (native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) _ hne))).trans
      (nodeRowExp_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l).symm)

/-- Ordinary leaf rows along a FALSE operation keep incoherency and order. -/
theorem nodeDat_leaf_false (con : LFConstruction (A.source i hcan hel htc hcc) false) (l : GLeaf A.skeleton.tree)
    (hl : l ≠ (A.family.placement i).retained) (hp : l ≠ A.skeleton.pair (A.family.placement i).retained) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        l.toNode = nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.toNode ∧
    nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        l.toNode = nodeRowExp A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.toNode := by
  have hne := pairOfLeaf_ne_exceptional A i hcan hel htc hcc l hl hp
  have hp' : (A.source i hcan hel htc hcc).pairs false (pairOfLeaf A.skeleton A.plain l) =
      pairOfLeaf A.skeleton A.plain l := pairOfLeaf_firstLeaf A.skeleton A.plain _
  have h1 := coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) _ hne
  have h2 := native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
    (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
    (stateLayer_spec (opOut A i hcan hel htc hcc con)) _ hne
  rw [hp'] at h1 h2
  refine ⟨(nodeRowIncoh_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) l).trans (h1.trans (nodeRowIncoh_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l).symm), ?_⟩
  exact (nodeRowExp_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) l).trans
    ((congrArg (fun LG : LayeredGarden 2 => 2 * LG.garden.order + 2) h2).trans (nodeRowExp_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l).symm)

/-- **The dart weight along a TRUE operation**, at every dart. -/
theorem ΨX_true (W : WD d) (con : LFConstruction (A.source i hcan hel htc hcc) true) (y : GardenDart A.skeleton) :
    ΨX W (opOut A i hcan hel htc hcc con) (twistDartEquiv A.skeleton (A.family.placement i) y) = ΨX W A y := by
  by_cases hy : IsExc (A.family.placement i) y
  · refine ΨX_eq_of W A (opOut A i hcan hel htc hcc con) y _ ((nodeRowIncoh_exc_true A i hcan hel htc hcc con hy).trans
      (nodeRowIncoh_exc_src A i hcan htc hcc hy).symm) (fun h => absurd (nodeRowIncoh_exc_src A i hcan htc hcc hy) h)
  · have hn : Mole.dartNode (unitTwistGarden A.skeleton (A.family.placement i))
        (twistDartEquiv A.skeleton (A.family.placement i) y) =
        naiveNodeEquiv A.skeleton (A.family.placement i) (Mole.dartNode A.skeleton y) := by
      rw [twist_eq_naive_of_not_exc (A.family.placement i) hy, dartNode_naive]
    rcases not_exc_cases (A.family.placement i) hy with ⟨c, s, rfl, hc⟩ | ⟨l, rfl, hl, hp⟩
    · have hn' : Mole.dartNode (unitTwistGarden A.skeleton (A.family.placement i))
          (twistDartEquiv A.skeleton (A.family.placement i) (.inl (c, s))) =
          (coreBranchEquiv A.skeleton (A.family.placement i) c.1).toNode :=
        hn.trans (naiveNodeEquiv_branch A.skeleton (A.family.placement i) c.1)
      obtain ⟨e1, e2⟩ := nodeDat_branch_true A i hcan hel htc hcc con c.1 hc
      exact ΨX_eq_of W A (opOut A i hcan hel htc hcc con) _ _ ((congrArg (nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) hn').trans e1)
        (fun _ => (congrArg (nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
          (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) hn').trans e2)
    · have hn' : Mole.dartNode (unitTwistGarden A.skeleton (A.family.placement i))
          (twistDartEquiv A.skeleton (A.family.placement i) (.inr l)) =
          (coreLeafEquiv A.skeleton (A.family.placement i) l.1).toNode :=
        hn.trans (naiveNodeEquiv_leaf A.skeleton (A.family.placement i) l.1)
      obtain ⟨e1, e2⟩ := nodeDat_leaf_true A i hcan hel htc hcc con l.1 hl hp
      exact ΨX_eq_of W A (opOut A i hcan hel htc hcc con) _ _ ((congrArg (nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) hn').trans e1)
        (fun _ => (congrArg (nodeRowExp (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
          (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) hn').trans e2)

/-- **The dart weight along a FALSE operation**, at every dart. -/
theorem ΨX_false (W : WD d) (con : LFConstruction (A.source i hcan hel htc hcc) false) (y : GardenDart A.skeleton) :
    ΨX W (opOut A i hcan hel htc hcc con) y = ΨX W A y := by
  by_cases hy : IsExc (A.family.placement i) y
  · obtain ⟨e1, e2⟩ := exc_out A i hcan hel htc hcc con
    have hp' : chosenPairEquiv A.skeleton (A.family.placement i) A.plain false
        (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained) =
        pairOfLeaf A.skeleton A.plain (A.family.placement i).retained := pairOfLeaf_firstLeaf A.skeleton A.plain _
    rw [hp'] at e2
    have h0 : nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (Mole.dartNode A.skeleton y) = 0 := by
      rcases exc_node (A.family.placement i) hy with h | h | h <;> rw [h]
      · exact (nodeRowIncoh_branch _ _ _ _ _).trans e1
      · exact (nodeRowIncoh_leaf _ _ _ _ _).trans e2
      · exact (nodeRowIncoh_leaf _ _ _ _ _).trans ((congrArg _ (pairOfLeaf_partner A.skeleton A.plain _)).trans e2)
    exact ΨX_eq_of W A (opOut A i hcan hel htc hcc con) y y (h0.trans (nodeRowIncoh_exc_src A i hcan htc hcc hy).symm)
      (fun h => absurd (nodeRowIncoh_exc_src A i hcan htc hcc hy) h)
  · rcases not_exc_cases (A.family.placement i) hy with ⟨c, s, rfl, hc⟩ | ⟨l, rfl, hl, hp⟩
    · obtain ⟨e1, e2⟩ := nodeDat_branch_false A i hcan hel htc hcc con c.1 hc
      exact ΨX_eq_of W A (opOut A i hcan hel htc hcc con) _ _ e1 (fun _ => e2)
    · obtain ⟨e1, e2⟩ := nodeDat_leaf_false A i hcan hel htc hcc con l.1 hl hp
      exact ΨX_eq_of W A (opOut A i hcan hel htc hcc con) _ _ e1 (fun _ => e2)

/-- Same chart: a FALSE operation keeps the weight of every block. -/
theorem bWN_false (W : WD d) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) false)
    (U : Finset (GBranch A.skeleton.tree)) :
    bWN W κ (opOut A i hcan hel htc hcc con) U = bWN W κ A U := by
  funext x
  unfold bWN bondWD
  refine Finset.prod_congr rfl fun y _ => ?_
  have e := ΨX_false A i hcan hel htc hcc W con y
  have l1 := layX_false A i hcan hel htc hcc con (A.skeleton.molecule.atom (A.skeleton.molecule.mate y))
  have l2 := layX_false A i hcan hel htc hcc con (A.skeleton.molecule.atom y)
  exact (congrFun (congrFun (congrFun e _) _) _).trans (congrFun (congrArg₂ (ΨX W A y) l1 l2) _)

/-- Rigid transport: a TRUE operation whose lower joint is outside the block. -/
theorem bWN_rigid (W : WD d) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {U : Finset (GBranch A.skeleton.tree)} (hlow : (A.family.placement i).lower ∉ U) (x') :
    bWN W κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U) x' =
      bWN W κ A U (fun y => x' (naiveNodeEquiv A.skeleton (A.family.placement i) y)) := by
  refine bondWD_transport (ΨX W A) κ.L κ.base (A.family.placement i) (ΨX W (opOut A i hcan hel htc hcc con))
    (layX A) (layX (opOut A i hcan hel htc hcc con)) U _ x'
    (fun y _ => ΨX_true A i hcan hel htc hcc W con y) (fun y hy => ?_)
    (fun v _ => layX_true A i hcan hel htc hcc con v)
  have hy' := mem_regionDarts.mp hy
  have hpc : ∀ s, y ≠ lowerPC A.skeleton (A.family.placement i) s := by
    intro s he
    subst he
    cases s
    · exact hlow hy'.1
    · exact hlow hy'.2
  have hlp : y ≠ retainedLP A.skeleton (A.family.placement i) := by
    intro he
    subst he
    exact hlow (atom_retainedLP (A.family.placement i) ▸ hy'.1)
  have hlp' : y ≠ A.skeleton.molecule.mate (retainedLP A.skeleton (A.family.placement i)) := by
    intro he
    subst he
    have h2 := hy'.2
    rw [A.skeleton.molecule.mate_mate] at h2
    exact hlow (atom_retainedLP (A.family.placement i) ▸ h2)
  unfold Mole.restrictLabels
  rw [twistDartEquiv_eq_naive (A.family.placement i) y hpc hlp hlp', dartNode_naive]

/-- The twist at the lower joint of the block (S side, and the bottom vine of a region). -/
theorem bWN_twist (W : WD d) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    (U : Finset (GBranch A.skeleton.tree)) (x : GNode A.skeleton.tree → Fin d → ℤ)
    (hx : PairedAt (A.family.placement i) x) :
    bWN W κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U)
        (twistNodeLabels A.skeleton (A.family.placement i) x) = bWN W κ A U x :=
  bondWD_transport (ΨX W A) κ.L κ.base (A.family.placement i) (ΨX W (opOut A i hcan hel htc hcc con))
    (layX A) (layX (opOut A i hcan hel htc hcc con)) U x _
    (fun y _ => ΨX_true A i hcan hel htc hcc W con y)
    (fun y _ => twist_bond_labels A.skeleton (A.family.placement i) x hx y)
    (fun v _ => layX_true A i hcan hel htc hcc con v)

/-- The twist above the block (T side): the labels are read through `twNode`. -/
theorem bWN_twNode (W : WD d) (κ : KPar d) (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {T : Finset (GBranch A.skeleton.tree)}
    (hpar : GNode.parent (A.family.placement i).lower.toNode (A.family.placement i).nonroot ∉ T)
    (hret : ¬ A.skeleton.molecule.InGroup T (retainedLP A.skeleton (A.family.placement i))) (x') :
    bWN W κ (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) T) x' =
      bWN W κ A T (fun y => x' (VineEstS4.twNode (A.family.placement i) y)) := by
  set P := A.family.placement i
  refine bondWD_transport (ΨX W A) κ.L κ.base P (ΨX W (opOut A i hcan hel htc hcc con))
    (layX A) (layX (opOut A i hcan hel htc hcc con)) T _ x'
    (fun y _ => ΨX_true A i hcan hel htc hcc W con y) (fun y hy => ?_)
    (fun v _ => layX_true A i hcan hel htc hcc con v)
  have hy' := mem_regionDarts.mp hy
  have hpc : ∀ s, y ≠ lowerPC A.skeleton P s := by
    intro s he
    subst he
    cases s
    · exact hpar hy'.2
    · exact hpar hy'.1
  have hlp : y ≠ retainedLP A.skeleton P := by
    intro he
    subst he
    exact hret hy'
  have hlp' : y ≠ A.skeleton.molecule.mate (retainedLP A.skeleton P) := by
    intro he
    subst he
    exact hret ((inGroup_mate_iff _).mp hy')
  have hn : Mole.dartNode A.skeleton y ≠ P.lower.toNode ∧ Mole.dartNode A.skeleton y ≠ P.retained.toNode := by
    cases y with
    | inl c =>
      obtain ⟨c, s⟩ := c
      have hc : c.1 ≠ P.lower := by
        intro hc
        have he : c = ⟨P.lower, P.nonroot⟩ := Subtype.ext hc
        subst he
        exact hpc s rfl
      exact ⟨fun h => hc (Mole.branch_toNode_injective h), Mole.branch_toNode_ne_leaf _ _⟩
    | inr l =>
      refine ⟨(Mole.branch_toNode_ne_leaf _ _).symm, fun h => hlp ?_⟩
      have hl : l.1 = P.retained := Mole.leaf_toNode_injective h
      have he : l = ⟨P.retained, P.unmarked, retained_nonroot A.skeleton P, P.paired_nonroot⟩ := Subtype.ext hl
      subst he
      rfl
  unfold Mole.restrictLabels
  rw [twistDartEquiv_eq_naive P y hpc hlp hlp', dartNode_naive]
  beta_reduce
  rw [VineEstS4.twNode_apply, Equiv.swap_apply_of_ne_of_ne hn.1 hn.2]

end Op

end WaveTurbulence.Flower.V5WB
