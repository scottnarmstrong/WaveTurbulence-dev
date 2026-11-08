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

/-- **T4.** The τ-class sum of the members' per-mode outer values, each with its OWN weighted unit kernels, equals the
outer value with the weighted class kernels `twistedRecenteredFWL` of the units. Unit `j` lies in one tree and carries
`gU j`, `SU j`. Hypotheses as in main's `sum_tauClass_vineD_api` (VINE-B♯ factorization `hV` is O3′'s T3). -/
def WeightedClassFactorizationL : Prop :=
  ∀ {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree} {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)}
    {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j)) (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j'))
    (_hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool} (T : Finset (LayeredGarden w))
    (_hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : Type*} (Wt : I → Ξ → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : I → Ξ → ReplacementSlot G → Mom d → ℂ) (frq : I → Ξ → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → List ℝ),
    (∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) →
    (∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))) →
    (∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ z, Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z)) →
    (∀ i ξ, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i ξ) (frq i ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ)) →
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFWL p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))

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

/-- **T4: the weighted class factorization** (weighted `VineC.sum_tauClass_vineD_api`). -/
theorem weightedClassFactorizationL : WeightedClassFactorizationL := by
  intro w S D hS layer hLayer J₀ instF instD U₀ a₀ b₀ R₀ n₀ B₀ hdisj₀ hprime p kind T hT V I instI sgn Ξ Wt d G L γ δ
    base roots tt lay hinges Zw hG amp frq route hclk hmom F gU SU hV hξ hint hsm
  rw [sum_layered_eq_sum_classU (Us := unitsSplit B₀) (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime
    (unitsRegion B₀ hdisj₀) T hT V, Finset.sum_congr rfl hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (hξ i)]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hfg : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      ∀ (j : J₀) (lam : ℤ) (t : Fin 3 → ℝ) (k : Fin 4 → Mom d),
        unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
            (k 0) (k 1) (k 2) (k 3) =
          recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
              ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
            twistedLocalKernelFWL p (gU j) (SU j)
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).1
              (classProd (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀) y j).2
              L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
    intro y hy j lam t k
    obtain ⟨M, _, hR⟩ := (mem_classU hprime).mp hy
    unfold unitRecenteredFWL
    rw [hR.sign_upper j, unitKernelFWL_classProd hprime ((mem_classU hprime).mp hy) j]
    rfl
  rw [sum_classU_outerValM (Us := unitsSplit B₀) (p := p) (kind := kind)
    (A := unitsStart B₀ hdisj₀ D hS layer hLayer) hprime (unitsRegion B₀ hdisj₀) G L γ δ base roots tt lay hinges Zw hG
    (amp i ξ) (frq i ξ) route hclk hmom _
    (fun j lam t k x => recPhase ((unitsStart B₀ hdisj₀ D hS layer hLayer).skeleton.sign
        ((unitsRegion B₀ hdisj₀) j).blk.a.toNode) L γ δ (t 0) (k 0) (k 1) (k 2) (k 3) *
      twistedLocalKernelFWL p (gU j) (SU j) x.1 x.2 L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2)
        (k 0) (k 1) (k 2) (k 3))
    hfg (hint i ξ) (hsm i ξ)]
  congr 1
  funext j lam t k
  unfold twistedRecenteredFWL
  exact (Finset.mul_sum _ _ _).symm

/-- **T4 with index-dependent mode types**, from V5W-0's `weightedClassFactorization` on `Σ i, Ξ i`. -/
theorem weightedClassFactorization_depL {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) {J₀ : Type} [Fintype J₀]
    [DecidableEq J₀] {U₀ : J₀ → Finset (GBranch S.tree)} {a₀ b₀ : J₀ → GBranch S.tree}
    {R₀ : ∀ j, CLRegionData S (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ} (B₀ : ∀ j, CLChainAssembly S (R₀ j) (n₀ j))
    (hdisj₀ : ∀ j j', j ≠ j' → Disjoint (U₀ j) (U₀ j')) (hprime : IsPrimeGarden S) {p : ℕ} {kind : Bool}
    (T : Finset (LayeredGarden w))
    (hT : (T : Set (LayeredGarden w)) = (unitsStart B₀ hdisj₀ D hS layer hLayer).allCoreOutputs (p := p) (kind := kind))
    (V : LayeredGarden w → ℂ) {I : Type*} [Fintype I] (sgn : I → ℂ) {Ξ : I → Type*} (Wt : ∀ i, Ξ i → ℂ) {d : ℕ}
    (G : Garden w) (L γ δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ)
    (lay : GBranch G.tree → ℕ) (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (hG : G.IsPlain) (amp : ∀ i, Ξ i → ReplacementSlot G → Mom d → ℂ) (frq : ∀ i, Ξ i → ReplacementSlot G → Fin 2 → ℤ)
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J₀) (hclk : J₀ → Fin 3 → ClkSrc G)
    (hmom : J₀ → Fin 4 → GNode G.tree) (F : I → J₀ → ℕ → Mom d → ℝ)
    (gU : J₀ → Mom d → ℂ) (SU : J₀ → List ℝ)
    (hV : ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      V y.1.layered = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)))
    (hξ : ∀ i, ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer) (unitsRegion B₀ hdisj₀),
      Summable (fun ξ : Ξ i => Wt i ξ *
        outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
          (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
            (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    (hint : ∀ i i' (ξ : Ξ i'), ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer)
        (unitsRegion B₀ hdisj₀), ∀ z,
      Integrable (outerIntegrandM G L γ δ base roots tt lay hG (amp i' ξ) (frq i' ξ) route hclk hmom
        (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z))
    (hsm : ∀ i i' (ξ : Ξ i'), ∀ y ∈ classU (unitsSplit B₀) p kind (unitsStart B₀ hdisj₀ D hS layer hLayer)
        (unitsRegion B₀ hdisj₀),
      Summable (fun z : GenDecoration G d roots 0 =>
        (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
          ∫ τ, outerIntegrandM G L γ δ base roots tt lay hG (amp i' ξ) (frq i' ξ) route hclk hmom
            (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
              (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ)) :
    ∑ LG ∈ T, V LG = ∑ i, sgn i * ∑' ξ : Ξ i, Wt i ξ *
      outerValM G L γ δ base roots tt lay hinges Zw hG (amp i ξ) (frq i ξ) route hclk hmom
        (fun j lam t k => twistedRecenteredFWL p (gU j) (SU j) S (a₀ j)
          (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
          L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) := by
  have key := weightedClassFactorizationL D hS layer hLayer B₀ hdisj₀ hprime T hT V sgn (Ξ := Σ i, Ξ i) (sigWt Wt)
    G L γ δ base roots tt lay hinges Zw hG (fun _ x => amp x.1 x.2) (fun _ x => frq x.1 x.2) route hclk hmom F gU SU
    (fun y hy => by
      rw [hV y hy]
      refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
      exact (tsum_sigWt_mul Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG (amp i' ξ) (frq i' ξ)
        route hclk hmom (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ (F i j) base (modW lam)
          (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i).symm)
    (fun i y hy => (summable_sigWt_mul_iff Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG
        (amp i' ξ) (frq i' ξ) route hclk hmom (fun j lam t k => unitRecenteredFWL p (gU j) (SU j) y.1 (y.2 j) L γ δ
          (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i).2 (hξ i y hy))
    (fun i x y hy z => hint i x.1 x.2 y hy z)
    (fun i x y hy => hsm i x.1 x.2 y hy)
  rw [key]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact tsum_sigWt_mul Wt (fun i' ξ => outerValM G L γ δ base roots tt lay hinges Zw hG (amp i' ξ) (frq i' ξ)
    route hclk hmom (fun j lam t k => twistedRecenteredFWL p (gU j) (SU j) S (a₀ j)
      (canonFinsetK p kind (startState (B₀ j) D hS layer hLayer) (chainStart (B₀ j)))
      L γ δ (F i j) base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) i

end WaveTurbulence.Flower.MkUnitsL
