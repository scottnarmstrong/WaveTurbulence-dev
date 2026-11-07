/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Twist
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Op1Step
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp6KT

/-! # FLAT-MOD (R60), kernel level 2: the modulated lower kernel under an LF operation at `p*`

`clLocalKernelModC_congr_data`, `clLocalKernelModC_twist_LF`, `clLocalKernelModC_false_LF`; `kTM`, the modulated lower kernel of a
split state (`VineEstS4.kT` with the modulation at the lower joint of the lower block); `kTM_op_true` / `kTM_op_false`: after an
operation at `p*` the lower kernel is that of the source with the first two boundary momenta exchanged (TRUE) or unchanged (FALSE).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C.Cont TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

section Congr
variable (R : CLRegionData G U a b) (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d) (lam : ℝ)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ clInteriorBranches R, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)

include hC hT hl in
theorem clLocalKernelModC_congr_data (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelModC D1 hG R L γ δ F layer1 hLayer1 base lam t0 t1 t2 e f g k =
      clLocalKernelModC D2 hG R L γ δ F layer2 hLayer2 base lam t0 t1 t2 e f g k := by
  unfold clLocalKernelModC
  congr 1
  refine tsum_congr fun κ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  congr 1
  unfold clLocalSummand
  have hstar : ∀ (κ' : GNode G.tree → (Fin d → ℤ)) (t' : Fin 3 → ℝ) (τ' : CLInternalTime R),
      clLocalStarProduct D1 hG R L γ δ F layer1 hLayer1 base κ' t' τ' =
        clLocalStarProduct D2 hG R L γ δ F layer2 hLayer2 base κ' t' τ' :=
    fun κ' t' τ' => clLocalStarProduct_congr_data R hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base hC hT κ' t' τ'
  simp only [hstar]
  rw [clLocalTimeDomain_congr_data R hG D1 D2 layer1 layer2 hl]

end Congr

section LF
variable {p : ℕ} {kind : Bool} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **K^{T,λ} twist invariance, TRUE-choice LF construction.** -/
theorem clLocalKernelModC_twist_LF (h : LFConstruction s true) {T : Finset (GBranch s.skeleton.tree)}
    {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z) (R' : TwRegion s.placement T z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelModC h.data (s.chosen_plain true) R' L γ δ F layer' hLayer' base lam t0 t1 t2 e f g k =
      clLocalKernelModC s.data s.plain R L γ δ F layer hLayer base lam t0 t1 t2 f e g k := by
  refine clLocalKernelModC_twist s.placement hB hCL R R' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base lam
    t0 t1 t2 e f g k ?_ ?_ ?_
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

/-- **K^{T,λ} invariance, FALSE-choice LF construction.** -/
theorem clLocalKernelModC_false_LF (h : LFConstruction s false) {T : Finset (GBranch s.skeleton.tree)}
    {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelModC h.data (s.chosen_plain false) R L γ δ F layer' hLayer' base lam t0 t1 t2 e f g k =
      clLocalKernelModC s.data s.plain R L γ δ F layer hLayer base lam t0 t1 t2 e f g k := by
  refine clLocalKernelModC_congr_data R s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base lam ?_ ?_ ?_
    t0 t1 t2 e f g k
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      have hq' := pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained
      rcases hq' with hq' | hq'
      · exact not_internal_retained s.placement hB hCL (hq' ▸ hint)
      · exact not_internal_pair s.placement hB hCL (hq' ▸ hint)
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rwa [hp] at this
  · intro v hv
    have hvl : v ≠ s.placement.lower := (Finset.mem_erase.mp hv).1
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

end LF

section Op
variable {ι : Type*} {p : ℕ} {kind : Bool} (A : FamilyReconstruction w ι) (i : ι)
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

/-- `K^{T,λ}` at the member `i` itself, TRUE operation: the first two boundary momenta are exchanged. -/
theorem kernelTM_op_true (con : LFConstruction (A.source i hcan hel htc hcc) true)
    {T : Finset (GBranch A.skeleton.tree)} {z : GBranch A.skeleton.tree}
    (hB : A.skeleton.molecule.IsBlock T (A.family.placement i).lower z)
    (hCL : Mole.CLParentPattern A.skeleton T (A.family.placement i).lower z)
    (R : CLRegionData A.skeleton T (A.family.placement i).lower z) (R' : TwRegion (A.family.placement i) T z)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelModC (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        R' L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base lam t0 t1 t2 e f g k =
      clLocalKernelModC A.data A.plain R L γ δ F (stateLayer A) (stateLayer_isLayering A) base lam t0 t1 t2 f e g k :=
  clLocalKernelModC_twist_LF (A.source i hcan hel htc hcc) con hB hCL R R' _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
    L γ δ F base lam t0 t1 t2 e f g k

/-- `K^{T,λ}` at the member `i` itself, FALSE operation: no exchange. -/
theorem kernelTM_op_false (con : LFConstruction (A.source i hcan hel htc hcc) false)
    {T : Finset (GBranch A.skeleton.tree)} {z : GBranch A.skeleton.tree}
    (hB : A.skeleton.molecule.IsBlock T (A.family.placement i).lower z)
    (hCL : Mole.CLParentPattern A.skeleton T (A.family.placement i).lower z)
    (R : CLRegionData A.skeleton T (A.family.placement i).lower z)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelModC (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
        R L γ δ F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
        (stateLayer_isLayering _) base lam t0 t1 t2 e f g k =
      clLocalKernelModC A.data A.plain R L γ δ F (stateLayer A) (stateLayer_isLayering A) base lam t0 t1 t2 e f g k :=
  clLocalKernelModC_false_LF (A.source i hcan hel htc hcc) con hB hCL R _ _ (stateLayer_spec A) _ _
    (stateLayer_spec (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)))
    L γ δ F base lam t0 t1 t2 e f g k

end Op

section KT
variable {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} (κ : KPar d) (lam : ℝ)
  (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)

/-- The modulated lower kernel `K^{T,λ}(t, t₁, t₂; E, F', g, h)` of a split state (`VineEstS4.kT` with the modulation at the lower
joint of the lower block). -/
noncomputable def kTM (X : FamilyReconstruction w ι) (sx : SplitAt X.skeleton X.family pstar J) : ℝ → Mom d → Mom d → ℂ :=
  fun t E F' =>
    clLocalKernelModC X.data X.plain sx.RT κ.L κ.γ κ.δ κ.F (stateLayer X) (stateLayer_isLayering X) κ.base lam t κ.t1 κ.t2
      E F' κ.g κ.h

variable (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

/-- A TRUE operation at `pstar` exchanges the first two boundary momenta of `K^{T,λ}`. -/
theorem kTM_op_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true) (t : ℝ) (E F' : Mom d) :
    kTM κ lam (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar))
      (SplitAt.nextA A sp pstar true) t E F' = kTM κ lam A sp t F' E := by
  have hb := SplitAt.joint_lower A sp
  unfold kTM
  have key : ∀ {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree}
      (hb : b = (A.family.placement pstar).lower) (hB : A.skeleton.molecule.IsBlock T b z)
      (hCL : Mole.CLParentPattern A.skeleton T b z) (R : CLRegionData A.skeleton T b z)
      (R' : CLRegionData (unitTwistGarden A.skeleton (A.family.placement pstar)) (twistedAtoms A.skeleton (A.family.placement pstar) T)
        (coreBranchEquiv A.skeleton (A.family.placement pstar) b) (coreBranchEquiv A.skeleton (A.family.placement pstar) z)),
      clLocalKernelModC (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)).plain
        R' κ.L κ.γ κ.δ κ.F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, true, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)))
        (stateLayer_isLayering _) κ.base lam t κ.t1 κ.t2 E F' κ.g κ.h =
      clLocalKernelModC A.data A.plain R κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base lam t κ.t1 κ.t2
        F' E κ.g κ.h := by
    intro T b z hb hB hCL R R'
    subst hb
    exact kernelTM_op_true A pstar hcan hel htc hcc con hB hCL R R' κ.L κ.γ κ.δ κ.F κ.base lam t κ.t1 κ.t2 E F' κ.g κ.h
  exact key hb sp.hT sp.clST.2 sp.RT (SplitAt.nextA A sp pstar true).RT

/-- A FALSE operation at `pstar` leaves `K^{T,λ}` unchanged. -/
theorem kTM_op_false (con : LFConstruction (A.source pstar hcan hel htc hcc) false) (t : ℝ) (E F' : Mom d) :
    kTM κ lam (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar))
      (SplitAt.nextA A sp pstar false) t E F' = kTM κ lam A sp t E F' := by
  have hb := SplitAt.joint_lower A sp
  unfold kTM
  have key : ∀ {T : Finset (GBranch A.skeleton.tree)} {b z : GBranch A.skeleton.tree}
      (hb : b = (A.family.placement pstar).lower) (hB : A.skeleton.molecule.IsBlock T b z)
      (hCL : Mole.CLParentPattern A.skeleton T b z) (R : CLRegionData A.skeleton T b z),
      clLocalKernelModC (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)).data
        (FamilyOperation.output (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)).plain
        R κ.L κ.γ κ.δ κ.F (stateLayer (FamilyOperation.output
          (⟨hcan, hel, htc, hcc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A pstar)))
        (stateLayer_isLayering _) κ.base lam t κ.t1 κ.t2 E F' κ.g κ.h =
      clLocalKernelModC A.data A.plain R κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A) κ.base lam t κ.t1 κ.t2
        E F' κ.g κ.h := by
    intro T b z hb hB hCL R
    subst hb
    exact kernelTM_op_false A pstar hcan hel htc hcc con hB hCL R κ.L κ.γ κ.δ κ.F κ.base lam t κ.t1 κ.t2 E F' κ.g κ.h
  have h := key hb sp.hT sp.clST.2 (SplitAt.nextA A sp pstar false).RT
  refine h.trans ?_
  rw [regionData_subsingleton (SplitAt.nextA A sp pstar false).RT sp.RT]

end KT

end WaveTurbulence.VineEstS5C.FlatMod
