/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.RowData

/-! # V5W-0: the region multiplier `regionWeightFW` along a foreign operation

`regionWeightFW` is the R135 bond product over the darts of the region whose row is coherent (masked by
`nodeRowIncoh = 0`), times the top filter `nodeWeight (topFilterWeight S)` at the region top.  For an operation whose
lower joint is outside the region:

* every dart of the region carries an ordinary node (`inGroup_dart_ordinary`): a branch other than the lower joint,
  or a leaf other than the retained leaf and its partner; so the twist dart bijection is the naive one there
  (`twistDartEquiv_eq_naive_of`), the bond labels and momenta are transported naively, and the masks are preserved
  (`nodeRowIncoh_opOut_true/_false`: the rows of ordinary nodes keep their incoherency, `RowData`);
* the core layers are carried by `LFConstruction.coreLayers`.

`regionWeightFW_true` (rigid TRUE operation) and `regionWeightFW_false` (FALSE operation) are the two transports used
by `UnitKernelFWForeign`.  The dart-node transport `dartNode_naive'` is the V5-SPACE-EXT lemma `dartNode_naive`
(uni-space `VineSpaceB/Bond.lean`, see `COPIED-SHA256SUMS`), re-proved verbatim.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 TTree
open WaveTurbulence.VineC WaveTurbulence.VineSpaceK WaveTurbulence.Flower.Stage1W

section Darts
variable {w d : ℕ} {G : Garden w} (P : CorePlacement G) {U : Finset (GBranch G.tree)}

theorem atom_retainedLP_eq : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P

/-- A dart with both ends in a region avoiding the lower joint carries an ordinary node. -/
theorem inGroup_dart_ordinary (hlow : P.lower ∉ U) (y : GardenDart G) (hy : G.molecule.InGroup U y) :
    (∃ (c : {c : GBranch G.tree // c.1.2 ≠ []}) (s : Bool), y = .inl (c, s) ∧ c.1 ∈ U ∧ c.1 ≠ P.lower) ∨
    (∃ l : {l : GLeaf G.tree // G.mark l = none ∧ l.1.2 ≠ [] ∧ (G.pair l).1.2 ≠ []},
      y = .inr l ∧ l.1 ≠ P.retained ∧ l.1 ≠ G.pair P.retained) := by
  rcases y with ⟨c, s⟩ | l
  · left
    have hc : c.1 ∈ U := by
      cases s
      · exact hy.1
      · exact hy.2
    exact ⟨c, s, rfl, hc, fun h => hlow (h ▸ hc)⟩
  · right
    refine ⟨l, rfl, fun h => ?_, fun h => ?_⟩
    · have he : l = ⟨P.retained, P.unmarked, retained_nonroot G P, P.paired_nonroot⟩ := Subtype.ext h
      subst he
      have h2 : G.molecule.atom (retainedLP G P) ∈ U := hy.1
      rw [atom_retainedLP_eq] at h2
      exact hlow h2
    · have hm : G.molecule.mate (Sum.inr l) = retainedLP G P := by
        show (Sum.inr _ : GardenDart G) = Sum.inr _
        exact congrArg Sum.inr (Subtype.ext (show G.pair l.1 = P.retained by rw [h, G.pair_pair]))
      have h2 : G.molecule.atom (G.molecule.mate (Sum.inr l)) ∈ U := hy.2
      rw [hm, atom_retainedLP_eq] at h2
      exact hlow h2

/-- Off the exceptional incidences the twist dart bijection is the naive carrier transport. -/
theorem twistDartEquiv_eq_naive_of (hlow : P.lower ∉ U) (y : GardenDart G) (hy : G.molecule.InGroup U y) :
    twistDartEquiv G P y = naiveDartEquiv G P y := by
  change naiveDartEquiv G P (exceptionalDartSwap G P y) = _
  congr 1
  rcases inGroup_dart_ordinary P hlow y hy with ⟨c, s, rfl, -, hc⟩ | ⟨l, rfl, hl, hp⟩
  · exact exceptionalDartSwap_otherPC G P c hc s
  · exact exceptionalDartSwap_otherLP G P l hl hp

/-- The naive carrier transport moves the carried node naively (V5-SPACE-EXT `dartNode_naive`). -/
theorem dartNode_naive' (y : GardenDart G) :
    Mole.dartNode (unitTwistGarden G P) (naiveDartEquiv G P y) = naiveNodeEquiv G P (Mole.dartNode G y) := by
  cases y with
  | inl c =>
    obtain ⟨c, s⟩ := c
    change (coreBranchEquiv G P c.1).toNode = naiveNodeEquiv G P c.1.toNode
    rw [naiveNodeEquiv_branch]
  | inr l =>
    change (coreLeafEquiv G P l.1).toNode = naiveNodeEquiv G P l.1.toNode
    rw [naiveNodeEquiv_leaf]

/-- **The masked bond product along a twist whose lower joint is outside the region.** -/
theorem maskedProd_naive (hlow : P.lower ∉ U) (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (inc : GNode G.tree → ℕ) (inc' : GNode (unitTwistGarden G P).tree → ℕ)
    (lay : GBranch G.tree → ℕ) (lay' : GBranch (unitTwistGarden G P).tree → ℕ)
    (hinc : ∀ y, G.molecule.InGroup U y → inc' (naiveNodeEquiv G P (Mole.dartNode G y)) = inc (Mole.dartNode G y))
    (hlay : ∀ v ∈ U, lay' (coreBranchEquiv G P v) = lay v) (x' : GNode (unitTwistGarden G P).tree → Fin d → ℤ) :
    (∏ y ∈ Finset.univ.filter ((unitTwistGarden G P).molecule.InGroup (twistedAtoms G P U)),
      if inc' (Mole.dartNode (unitTwistGarden G P) y) = 0 then
        ψ (lay' ((unitTwistGarden G P).molecule.atom ((unitTwistGarden G P).molecule.mate y)))
          (lay' ((unitTwistGarden G P).molecule.atom y))
          (cosetDecoration (unitTwistGarden G P) L base x' (Mole.dartNode (unitTwistGarden G P) y))
      else 1) =
    ∏ y ∈ Finset.univ.filter (G.molecule.InGroup U),
      if inc (Mole.dartNode G y) = 0 then
        ψ (lay (G.molecule.atom (G.molecule.mate y))) (lay (G.molecule.atom y))
          (cosetDecoration G L base (fun n => x' (naiveNodeEquiv G P n)) (Mole.dartNode G y))
      else 1 := by
  symm
  refine Finset.prod_equiv (twistDartEquiv G P) (fun y => ?_) (fun y hy => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Molecule.InGroup, twistDartEquiv_atom,
      twistDartEquiv_mate]
    exact and_congr (mem_twistedAtoms G P U _).symm (mem_twistedAtoms G P U _).symm
  · have hy' : G.molecule.InGroup U y := (Finset.mem_filter.mp hy).2
    rw [twistDartEquiv_mate, twistDartEquiv_atom, twistDartEquiv_atom, hlay _ hy'.1, hlay _ hy'.2,
      twistDartEquiv_eq_naive_of P hlow y hy', dartNode_naive', hinc y hy']
    rfl

end Darts

section Op
variable {w d : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
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

/-- An operation keeps the core layers along the chosen branch bijection. -/
theorem stateCoreLayer_opOut {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε)
    (v : GBranch A.skeleton.tree) :
    stateCoreLayer (opOut A i hcan hel htc hcc con) (chosenBranchEquiv A.skeleton (A.family.placement i) ε v) =
      stateCoreLayer A v :=
  (con.coreLayers v).symm

/-- The transported pair of the source pair of a leaf is the source pair of the transported leaf. -/
theorem tp_pairOfLeaf {G : Garden w} (P : CorePlacement G) (hG : G.IsPlain) (l : GLeaf G.tree) :
    tp P hG (pairOfLeaf G hG l) =
      pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (coreLeafEquiv G P l) := by
  change pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG)
    (coreLeafEquiv G P ((pairOfLeaf G hG l).firstLeaf hG)) = _
  rcases pairOfLeaf_first_or_partner G hG l with h | h
  · rw [h]
  · rw [h]
    exact (congrArg (pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG))
      (unitTwistGarden_pair G P l).symm).trans
      (pairOfLeaf_partner (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (coreLeafEquiv G P l))

/-- The source pair of an ordinary leaf is not the exceptional pair. -/
theorem pairOfLeaf_ne_exceptional (l : GLeaf A.skeleton.tree) (hl : l ≠ (A.family.placement i).retained)
    (hp : l ≠ A.skeleton.pair (A.family.placement i).retained) :
    pairOfLeaf A.skeleton A.plain l ≠ (A.source i hcan hel htc hcc).exceptional := by
  intro he
  rcases eq_or_pair_of_pairOfLeaf A.plain he with h | h
  · exact hl h
  · exact hp h

/-- The mask of an ordinary node along a TRUE operation. -/
theorem nodeRowIncoh_opOut_true (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {U : Finset (GBranch A.skeleton.tree)} (hlow : (A.family.placement i).lower ∉ U)
    (y : GardenDart A.skeleton) (hy : A.skeleton.molecule.InGroup U y) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (naiveNodeEquiv A.skeleton (A.family.placement i) (Mole.dartNode A.skeleton y)) =
      nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) (Mole.dartNode A.skeleton y) := by
  rcases inGroup_dart_ordinary (A.family.placement i) hlow y hy with ⟨c, s, rfl, -, hc⟩ | ⟨l, rfl, hl, hp⟩
  · change nodeRowIncoh _ _ _ _ (naiveNodeEquiv A.skeleton (A.family.placement i) c.1.toNode) =
      nodeRowIncoh _ _ _ _ c.1.toNode
    rw [naiveNodeEquiv_branch]
    exact (nodeRowIncoh_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (coreBranchEquiv A.skeleton (A.family.placement i) c.1)).trans
      ((treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (stateLayer_spec (opOut A i hcan hel htc hcc con)) c.1 hc).trans (nodeRowIncoh_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.1).symm)
  · change nodeRowIncoh _ _ _ _ (naiveNodeEquiv A.skeleton (A.family.placement i) l.1.toNode) =
      nodeRowIncoh _ _ _ _ l.1.toNode
    rw [naiveNodeEquiv_leaf]
    have := coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (stateLayer_spec (opOut A i hcan hel htc hcc con)) (pairOfLeaf A.skeleton A.plain l.1)
      (pairOfLeaf_ne_exceptional A i hcan hel htc hcc l.1 hl hp)
    exact (nodeRowIncoh_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (coreLeafEquiv A.skeleton (A.family.placement i) l.1)).trans
      (((congrArg (coupleIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)))
        (tp_pairOfLeaf (A.family.placement i) A.plain l.1).symm).trans this).trans
        (nodeRowIncoh_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.1).symm)

/-- The mask of an ordinary node along a FALSE operation. -/
theorem nodeRowIncoh_opOut_false (con : LFConstruction (A.source i hcan hel htc hcc) false)
    {U : Finset (GBranch A.skeleton.tree)} (hlow : (A.family.placement i).lower ∉ U)
    (y : GardenDart A.skeleton) (hy : A.skeleton.molecule.InGroup U y) :
    nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) (Mole.dartNode A.skeleton y) =
      nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A) (Mole.dartNode A.skeleton y) := by
  rcases inGroup_dart_ordinary (A.family.placement i) hlow y hy with ⟨c, s, rfl, -, hc⟩ | ⟨l, rfl, hl, hp⟩
  · change nodeRowIncoh _ _ _ _ c.1.toNode = nodeRowIncoh _ _ _ _ c.1.toNode
    exact (nodeRowIncoh_branch (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) c.1).trans
      ((treeIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
        (stateLayer_spec (opOut A i hcan hel htc hcc con)) c.1 hc).trans (nodeRowIncoh_branch A.data A.plain (stateLayer A) (stateLayer_isLayering A) c.1).symm)
  · change nodeRowIncoh _ _ _ _ l.1.toNode = nodeRowIncoh _ _ _ _ l.1.toNode
    have := coupleIncoh_LF con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))
      (stateLayer_spec (opOut A i hcan hel htc hcc con)) (pairOfLeaf A.skeleton A.plain l.1)
      (pairOfLeaf_ne_exceptional A i hcan hel htc hcc l.1 hl hp)
    have hp' : (A.source i hcan hel htc hcc).pairs false (pairOfLeaf A.skeleton A.plain l.1) =
        pairOfLeaf A.skeleton A.plain l.1 :=
      pairOfLeaf_firstLeaf A.skeleton A.plain _
    exact (nodeRowIncoh_leaf (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)) l.1).trans
      (((congrArg (coupleIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con))) hp'.symm).trans this).trans
        (nodeRowIncoh_leaf A.data A.plain (stateLayer A) (stateLayer_isLayering A) l.1).symm)

/-- The top filter (any node weight at the region top) along a rigid twist. -/
theorem nodeWeight_naive {G : Garden w} (P : CorePlacement G) {U : Finset (GBranch G.tree)} (hF : FullRigid P U)
    {a : GBranch G.tree} (ha : a ∈ U) (Wt : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (x' : GNode (unitTwistGarden G P).tree → Fin d → ℤ) :
    nodeWeight Wt L base (eB P a) x' = nodeWeight Wt L base a (fun y => x' (naiveNodeEquiv G P y)) := by
  have e0 : cosetDecoration (unitTwistGarden G P) L base x' (eB P a).toNode =
      cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) a.toNode := by
    unfold cosetDecoration
    exact congrArg (fun y => base + latticePoint L y) (congrArg x' (naiveNodeEquiv_branch G P a).symm)
  have ej : ∀ j : Fin 3, cosetDecoration (unitTwistGarden G P) L base x' ((eB P a).child j) =
      cosetDecoration G L base (fun y => x' (naiveNodeEquiv G P y)) (a.child j) := by
    intro j
    unfold cosetDecoration
    exact congrArg (fun y => base + latticePoint L y) (congrArg x' (hF.child_naive ha j).symm)
  unfold nodeWeight
  rw [e0, ej 0, ej 1, ej 2]

/-- The masked bond product of a region reads the masks and the layers only at the darts of the region. -/
theorem maskedProd_congr {G : Garden w} (U : Finset (GBranch G.tree)) (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ)
    (base : Mom d) (inc inc' : GNode G.tree → ℕ) (lay lay' : GBranch G.tree → ℕ)
    (hinc : ∀ y, G.molecule.InGroup U y → inc' (Mole.dartNode G y) = inc (Mole.dartNode G y))
    (hlay : ∀ v ∈ U, lay' v = lay v) (x : GNode G.tree → Fin d → ℤ) :
    (∏ y ∈ Finset.univ.filter (G.molecule.InGroup U),
      if inc' (Mole.dartNode G y) = 0 then
        ψ (lay' (G.molecule.atom (G.molecule.mate y))) (lay' (G.molecule.atom y))
          (cosetDecoration G L base x (Mole.dartNode G y))
      else 1) =
    ∏ y ∈ Finset.univ.filter (G.molecule.InGroup U),
      if inc (Mole.dartNode G y) = 0 then
        ψ (lay (G.molecule.atom (G.molecule.mate y))) (lay (G.molecule.atom y))
          (cosetDecoration G L base x (Mole.dartNode G y))
      else 1 := by
  refine Finset.prod_congr rfl fun y hy => ?_
  have hy' : G.molecule.InGroup U y := (Finset.mem_filter.mp hy).2
  rw [hinc y hy', hlay _ hy'.1, hlay _ hy'.2]

end Op

end WaveTurbulence.Flower.V5W
