/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.MemberL
public import WaveTurbulence.Foundations.Flower.V5W.Foreign
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WClass

/-! # MK-UNITS-L (B3-2): list-T4, the weighted class factorization with per-unit top filters

V5W-0's T4 (`V5W/Foreign.lean`, statements `V5W/Statements.lean` §6) with the top filter `S : Option ℝ` replaced by
V5W-2L's product filter `S : List ℝ` (kernels `unitKernelFWL`, `twistedLocalKernelFWL`, `twistedRecenteredFWL`,
`unitRecenteredFWL`), and Stage1WVine's index-dependent form `weightedClassFactorization_dep`:

* `regionWeightFWL_true`, `regionWeightFWL_false`: the region multiplier along a foreign operation (V5W's
  `regionWeightFW_true/_false`, verbatim: the top filter is any node weight, `nodeWeight_naive`);
* `unitKernelFWL_foreign : UnitKernelFWForeignL`, `reachU_kernelFWL_eq`, `coordFWL_exists`, `unitKernelFWL_classProd`;
* `weightedClassFactorizationL : WeightedClassFactorizationL` (per-unit filters `SU : J₀ → List ℝ`);
* `weightedClassFactorization_depL`.

Copied by source from `Flower/V5W/Weight.lean` (§Op), `Flower/V5W/Statements.lean` (§6), `Flower/V5W/Foreign.lean`,
`Flower/Stage1WVine/WClass.lean` (see `COPIED-SHA256SUMS`), threaded with `S : List ℝ` (ruling R179, wt-orch: list-T4
built inside MkUnitsL).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnitsL
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 TTree MeasureTheory
  WaveTurbulence.Represents WaveTurbulence.LGSpine WaveTurbulence.VineEstS2
open WaveTurbulence.VineC WaveTurbulence.VineSpaceK WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W
open WaveTurbulence.Flower.V5W2L (topFilterWeightL regionWeightFWL twistedLocalKernelFWL twistedRecenteredFWL
  unitKernelFWL unitRecenteredFWL)
open WaveTurbulence.Flower.Stage1WVine (sigWt tsum_sigWt_mul summable_sigWt_mul_iff)
open WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineSpaceB VineEstS5C.P4.Final Cut2A
  WaveTurbulence.RedSplice WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineB
open scoped ENNReal FourierTransform

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

/-- **`regionWeightFWL` along a rigid TRUE operation.** -/
theorem regionWeightFWL_true (con : LFConstruction (A.source i hcan hel htc hcc) true) (pw : ℕ) (g : Mom d → ℂ)
    (S : List ℝ) (L : ℝ) (base : Mom d) {U : Finset (GBranch A.skeleton.tree)} {a : GBranch A.skeleton.tree}
    (hF : FullRigid (A.family.placement i) U) (ha : a ∈ U)
    (x' : GNode (unitTwistGarden A.skeleton (A.family.placement i)).tree → Fin d → ℤ) :
    regionWeightFWL pw g S L base (opOut A i hcan hel htc hcc con) (twistedAtoms A.skeleton (A.family.placement i) U)
        (coreBranchEquiv A.skeleton (A.family.placement i) a) x' =
      regionWeightFWL pw g S L base A U a (fun y => x' (naiveNodeEquiv A.skeleton (A.family.placement i) y)) := by
  unfold regionWeightFWL
  refine congrArg₂ (· * ·) ?_ ?_
  · exact maskedProd_naive (A.family.placement i) hF.lower_notMem (topPsi pw g) L base
      (nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A))
      (nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
        (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)))
      (stateCoreLayer A) (stateCoreLayer (opOut A i hcan hel htc hcc con))
      (nodeRowIncoh_opOut_true A i hcan hel htc hcc con hF.lower_notMem)
      (fun v _ => stateCoreLayer_opOut A i hcan hel htc hcc con v) x'
  · exact nodeWeight_naive (A.family.placement i) hF ha (topFilterWeightL S) L base x'

/-- **`regionWeightFWL` along a FALSE operation whose lower joint is outside the region.** -/
theorem regionWeightFWL_false (con : LFConstruction (A.source i hcan hel htc hcc) false) (pw : ℕ) (g : Mom d → ℂ)
    (S : List ℝ) (L : ℝ) (base : Mom d) {U : Finset (GBranch A.skeleton.tree)} (a : GBranch A.skeleton.tree)
    (hlow : (A.family.placement i).lower ∉ U) (x : GNode A.skeleton.tree → Fin d → ℤ) :
    regionWeightFWL pw g S L base (opOut A i hcan hel htc hcc con) U a x = regionWeightFWL pw g S L base A U a x := by
  unfold regionWeightFWL
  refine congrArg₂ (· * ·) ?_ rfl
  exact maskedProd_congr U (topPsi pw g) L base
    (nodeRowIncoh A.data A.plain (stateLayer A) (stateLayer_isLayering A))
    (nodeRowIncoh (opOut A i hcan hel htc hcc con).data (opOut A i hcan hel htc hcc con).plain
      (stateLayer (opOut A i hcan hel htc hcc con)) (stateLayer_isLayering (opOut A i hcan hel htc hcc con)))
    (stateCoreLayer A) (stateCoreLayer (opOut A i hcan hel htc hcc con))
    (nodeRowIncoh_opOut_false A i hcan hel htc hcc con hlow)
    (fun v _ => stateCoreLayer_opOut A i hcan hel htc hcc con v) x

end Op

/-- T4's key lemma (weighted `VineC.unitKernelW_foreign`): an operation at a member outside the unit leaves the unit's
weighted kernel unchanged (rows rigid, core layers preserved, region darts untouched). -/
def UnitKernelFWForeignL : Prop :=
  ∀ {w : ℕ} {ι : Type*} {Q : ι → Prop} {p : ℕ} {kind : Bool} {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : List ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q) {i : ι}
    (_hi : ¬ Q i) (op : FamilyOperation (p := p) (kind := kind) X i)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d),
    unitKernelFWL pw g S op.output (u.nextA X i op.choice) L γ δ F base W t0 t1 t2 e f g' h =
      unitKernelFWL pw g S X u L γ δ F base W t0 t1 t2 e f g' h

/-- **T4's key lemma** (weighted `VineC.unitKernelW_foreign`). -/
theorem unitKernelFWL_foreign : UnitKernelFWForeignL := by
  intro w ι Q p kind d pw g S X u i hi op L γ δ F base W t0 t1 t2 e f g' h
  have hF := fullRigid_of_disjoint X.family (u.disj i hi)
  obtain ⟨hcan, hel, htc, hcc, ε, con⟩ := op
  cases ε
  · exact clLocalKernelFW_false_LF (X.source i hcan hel htc hcc) con u.blk.block hF.lower_notMem
      (clRegionData X.skeleton u.blk.block u.cl) (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (opOut X i hcan hel htc hcc con)) pw g L γ δ F base _ _
      (fun z => regionWeightFWL_false X i hcan hel htc hcc con pw g S L base u.blk.a hF.lower_notMem z)
      W t0 t1 t2 e f g' h
  · exact clLocalKernelFW_rigid_LF (X.source i hcan hel htc hcc) con u.blk.block hF
      (clRegionData X.skeleton u.blk.block u.cl) _ (stateLayer X) (stateLayer_isLayering X) (stateLayer_spec X) _ _
      (stateLayer_spec (opOut X i hcan hel htc hcc con)) pw g L γ δ F base _ _
      (fun z' => regionWeightFWL_true X i hcan hel htc hcc con pw g S L base hF u.blk.block.2.1 z')
      W t0 t1 t2 e f g' h

section Reach
variable {w : ℕ} {ι : Type*} {J : Type*} {Qm : J → ι → Prop} {p : ℕ} {kind : Bool}

/-- Along a batch avoiding the unit `j`, the weighted kernel of the unit `j` is unchanged. -/
theorem reachU_kernelFWL_eq {Lst : List ι} {A B : FamilyReconstruction w ι}
    {us : ∀ j, UnitAt A.skeleton A.family (Qm j)} {us' : ∀ j, UnitAt B.skeleton B.family (Qm j)}
    (hR : ReachU p kind Qm Lst A us B us') (j : J) (hL : ∀ i ∈ Lst, ¬ Qm j i) {d : ℕ} (pw : ℕ) (g : Mom d → ℂ)
    (S : List ℝ) (L' γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    unitKernelFWL pw g S B (us' j) L' γ δ F base W t0 t1 t2 e f g' k =
      unitKernelFWL pw g S A (us j) L' γ δ F base W t0 t1 t2 e f g' k := by
  induction hR with
  | nil A us => rfl
  | skip i h ih => exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
  | @apply Lst A us B us' i op h ih =>
    refine (ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))).trans ?_
    exact unitKernelFWL_foreign pw g S A (us j) (hL i List.mem_cons_self) op L' γ δ F base W t0 t1 t2 e f g' k

end Reach

section Proj
variable {w : ℕ} {ι κ : Type*} (e : κ → ι) (he : Function.Injective e) {Q : ι → Prop} (hQ : ∀ k, Q (e k))

/-- The weighted unit kernel of the big state is the weighted twisted kernel of the restricted state. -/
theorem unitKernelFWL_eq_twisted {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : List ℝ) (X : FamilyReconstruction w ι)
    (u : UnitAt X.skeleton X.family Q) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ)
    (e' f g' h : Mom d) :
    unitKernelFWL pw g S X u L γ δ F base W t0 t1 t2 e' f g' h =
      twistedLocalKernelFWL pw g S (stComap X e he) (u.toChainAt e he hQ) L γ δ F base W t0 t1 t2 e' f g' h := rfl

end Proj

section Coord
variable {w : ℕ} {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J] {κ : J → Type*}
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Us : UnitSplit ι J κ} {p : ℕ} {kind : Bool}

omit [Fintype J] in
/-- **Existence of the unit coordinates, with the weighted unit kernel read at the coordinate** (weighted
`VineC.coord_exists`). -/
theorem coordFWL_exists {A : FamilyReconstruction w ι} {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)}
    {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J) :
    ∃ x, IsCoord Us p kind A us y j x ∧
      ∀ {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ)
        (t0 t1 t2 : ℝ) (e f g' h : Mom d),
        twistedLocalKernelFWL pw g S x.1 x.2 L γ δ F base W t0 t1 t2 e f g' h =
          unitKernelFWL pw g S y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g' h := by
  obtain ⟨B, usB⟩ := y
  obtain ⟨M, hM, hR⟩ := hy
  dsimp only at hR ⊢
  have hMn : M.Nodup := perm_univ_nodup hM
  obtain ⟨Y, h1, h2⟩ := batch_partition (fun i => decide (Us.unitOf i = j)) M hMn hR.batch
  obtain ⟨usY, hRY⟩ := batch_reachU (Qm := Us.Q) h1 us
  obtain ⟨us'', hR2⟩ := batch_reachU (Qm := Us.Q) h2 usY
  have hn2 : (M.filter (fun i => decide (Us.unitOf i = j)) ++
      M.filter (fun i => !decide (Us.unitOf i = j))).Nodup :=
    (List.filter_append_perm (fun i => decide (Us.unitOf i = j)) M).nodup_iff.mpr hMn
  have hus : us'' = usB := ReachU.unique hn2 hMn (hRY.append hR2) hR
  subst hus
  obtain ⟨N, hN, hNe⟩ := Us.filter_eq_map j hM
  have hRY' : ReachU p kind Us.Q (N.map (Us.emb j)) A us Y usY := by rw [hNe]; exact hRY
  have hproj := ReachU.proj (Us.emb j) (Us.inj j) j (Us.q_emb j) N hRY'
  have hnot : ∀ i ∈ M.filter (fun i => !decide (Us.unitOf i = j)), ¬ Us.Q j i := by
    intro i hi hq
    have := (List.mem_filter.mp hi).2
    simp only [UnitSplit.Q] at hq
    simp [hq] at this
  refine ⟨⟨stComap Y (Us.emb j) (Us.inj j), (usY j).toChainAt (Us.emb j) (Us.inj j) (Us.q_emb j)⟩,
    ⟨⟨N, hN, hproj⟩, fun k => ?_⟩, fun pw g S L γ δ F base W t0 t1 t2 e f g' h => ?_⟩
  · show sigStar Y (Us.emb j k) = sigStar B (Us.emb j k)
    exact (sigStar_batch h2 (fun hm => hnot _ hm (Us.q_emb j k))).symm
  · exact (unitKernelFWL_eq_twisted (Us.emb j) (Us.inj j) (Us.q_emb j) pw g S Y (usY j) L γ δ F base W t0 t1 t2
      e f g' h).symm.trans (reachU_kernelFWL_eq hR2 j hnot pw g S L γ δ F base W t0 t1 t2 e f g' h).symm

omit [Fintype J] in
/-- **The weighted unit kernel of a class member is the weighted kernel of its unit coordinate** (TARGET L1948,
observation 1; weighted `VineC.unitKernelW_classProd`). -/
theorem unitKernelFWL_classProd {A : FamilyReconstruction w ι} (hA : IsPrimeGarden A.skeleton)
    {us : ∀ j, UnitAt A.skeleton A.family (Us.Q j)} {y : UState w Us} (hy : y ∈ ClassUSet Us p kind A us) (j : J)
    {d : ℕ} (pw : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ)
    (t0 t1 t2 : ℝ) (e f g' h : Mom d) :
    unitKernelFWL pw g S y.1 (y.2 j) L γ δ F base W t0 t1 t2 e f g' h =
      twistedLocalKernelFWL pw g S (classProd Us p kind A us y j).1 (classProd Us p kind A us y j).2 L γ δ F base W
        t0 t1 t2 e f g' h := by
  obtain ⟨x, hx, hk⟩ := coordFWL_exists hy j
  rw [coord_unique hA (classProd_isCoord hy j) hx]
  exact (hk pw g S L γ δ F base W t0 t1 t2 e f g' h).symm

end Coord

end WaveTurbulence.Flower.MkUnitsL
