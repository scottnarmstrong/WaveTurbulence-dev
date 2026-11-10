/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCRigid1

/-! # VINE-C: the weighted unit kernel is invariant under a unit twist elsewhere (TARGET L1948, observation 1)

`clLocalKernelW … W …` is `clLocalKernel` (TARGET L1733–L1740) with the integrand multiplied by `W(τ_b)`, a weight of the
clock of the lower joint `b` of the region.  `W = 1` is `clLocalKernel` (`clLocalKernelW_one`); `W = modW λ`,
`s ↦ e^{πiλs}`, is the modulated unit kernel of ruling R58 (F-LOWCLOCK, INTERFACE v2): the factor `e^{πiλτ_b}` in the
internal integrand.

* `clLocalKernelW_rigid`: for a region `U` that the unit twist `P` moves rigidly (`FullRigid`), the kernel of the twisted
  garden at the transported region equals the kernel of `G` at `U`, with the SAME boundary momenta and clocks, provided the
  native rows and the atom layers of the region agree (`hC`, `hT`, `hl`).
* `clLocalKernelW_congr_data`: same skeleton, native rows and layers agree (a FALSE-choice operation elsewhere).
* `clLocalKernelW_rigid_LF`, `clLocalKernelW_false_LF`: the LF-level statements (rows from `native_couple_eq`,
  `native_tree_eq`, `coreLayer_eq`); only `P.lower ∉ U` is needed in the false case.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineC
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.VineEstS4 TTree MeasureTheory

/-- The unit kernel with a weight `W` of the clock of the lower joint `b` in the internal integrand. -/
@[expose] noncomputable def clLocalKernelW {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (W : ℝ → ℂ)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e, f, g, h],
      ∫ τ : CLInternalTime R,
        clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![tUpper, tPositive, tNegative] κ τ *
          W (clLocalClock R ![tUpper, tPositive, tNegative] τ b)

/-- The modulation `s ↦ e^{πiλs}` (R58). -/
@[expose] noncomputable def modW (lam : ℝ) : ℝ → ℂ := fun s => Complex.exp (((Real.pi * lam * s : ℝ) : ℂ) * Complex.I)

variable {w : ℕ} {G : Garden w} {P : CorePlacement G} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  (hB : G.molecule.IsBlock U a b) (hF : FullRigid P U)
  (R : CLRegionData G U a b) (R' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P U) (eB P a) (eB P b))

section Domain

include hB hF in
/-- The local time domains correspond under the identification of the internal times. -/
theorem domain_iff_rigid (ℓ : GBranch G.tree → ℕ) (ℓ' : GBranch (unitTwistGarden G P).tree → ℕ)
    (hℓ : ∀ v ∈ U, ℓ' (eB P v) = ℓ v) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    tEquivS P R R' τ ∈ clLocalTimeDomain R' ℓ' t ↔ τ ∈ clLocalTimeDomain R ℓ t := by
  obtain ⟨_, _, hp, hn⟩ := region_eq_rigid hB hF R R'
  have hR := hF.rigidAt b
  have hbU : b ∈ U := hB.2.2.1
  have hclock := fun v (hv : v ∈ U) => clockS_corr P R R' t τ hv
  have e3 : ∀ v : ↥(clInteriorBranches R),
      parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ)) (iBS P R R' v).1.toNode =
        parentClock (t 0) (clLocalClock R t τ) v.1.toNode := by
    intro v
    have hvT := Finset.mem_of_mem_erase v.2
    have hva : v.1.toNode ≠ a.toNode := fun h => (Finset.mem_erase.mp v.2).1 (Mole.branch_toNode_injective h)
    have := parentClock_rigid P hB hR R (t 0) (clLocalClock R' t (tEquivS P R R' τ)) (clLocalClock R t τ)
      (fun v hv => hclock v hv) ((branch_mem_clRealizationNodes v.1).mpr hvT) hva
    exact (congrArg (parentClock (t 0) (clLocalClock R' t (tEquivS P R R' τ)))
      (naiveNodeEquiv_branch G P v.1).symm).trans this
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro H v
      have hv := H (iBS P R R' v)
      have e1 : ℓ' (iBS P R R' v).1 = ℓ v.1 := hℓ v.1 (Finset.mem_of_mem_erase v.2)
      have e2 : tEquivS P R R' τ (iBS P R R' v) = τ v := tEquivS_apply P R R' τ v
      rw [e1, e2, e3 v] at hv
      exact hv
    · intro H v'
      obtain ⟨v, rfl⟩ := (iBS P R R').surjective v'
      have hv := H v
      have e1 : ℓ' (iBS P R R' v).1 = ℓ v.1 := hℓ v.1 (Finset.mem_of_mem_erase v.2)
      have e2 : tEquivS P R R' τ (iBS P R R' v) = τ v := tEquivS_apply P R R' τ v
      rw [e1, e2, e3 v]
      exact hv
  · have hc := hF.child_naive hbU R.positive
    have hb := branching_naive P (b.child R.positive)
    have hv : (naiveNodeEquiv G P (b.child R.positive)).1 = ((eB P b).child R.positive).1 := congrArg Subtype.val hc
    rw [hv] at hb
    have hcl := hclock b hbU
    rw [hp]
    constructor
    · intro H hA
      have := H (hb.mp hA)
      rwa [hcl] at this
    · intro H hA
      have := H (hb.mpr hA)
      rwa [← hcl] at this
  · have hc := hF.child_naive hbU R.negative
    have hb := branching_naive P (b.child R.negative)
    have hv : (naiveNodeEquiv G P (b.child R.negative)).1 = ((eB P b).child R.negative).1 := congrArg Subtype.val hc
    rw [hv] at hb
    have hcl := hclock b hbU
    rw [hn]
    constructor
    · intro H hA
      have := H (hb.mp hA)
      rwa [hcl] at this
    · intro H hA
      have := H (hb.mpr hA)
      rwa [← hcl] at this

end Domain

section Summand
variable {d : ℕ} (hG : G.IsPlain) (D : ReconstructionData G) (D' : ReconstructionData (unitTwistGarden G P))
  (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d) (β : Fin 4 → Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (tp P hG p) =
      nativeCoupleLayered D hG layer hLayer p)
  (hT : ∀ v ∈ U.erase a, nativeChainLayered D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P v) =
      nativeChainLayered D hG layer hLayer v)
  (hl : ∀ v ∈ U, layer' (D'.coreBranch (unitTwistGarden_plain G P hG) (eB P v)).toNode =
      layer (D.coreBranch hG v).toNode)

include hB hF hC hT hl in
/-- **The local summand is invariant under a rigid twist** (no exchange of the boundary momenta). -/
theorem summand_rigid (t : Fin 3 → ℝ) (κ' : CLLocalDecoration R' L base β) (τ : CLInternalTime R) :
    clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base β t κ' (tEquivS P R R' τ) =
      clLocalSummand D hG R L γ δ F layer hLayer base β t (decEquivR hB hF R R' L base β κ') τ := by
  set κ := decEquivR hB hF R R' L base β κ' with hκ
  have hR := hF.rigidAt b
  have hRl := hF.rigidAt P.lower
  have hext : clExtendIndices R κ.1 = fun y => clExtendIndices R' κ'.1 (naiveNodeEquiv G P y) :=
    funext fun x => decEquivR_ext hB hF R R' L base β κ' x
  have hclock := fun v (hv : v ∈ U) => clockS_corr P R R' t τ hv
  have heps : clRegionalEpsilon (unitTwistGarden G P) (twistedAtoms G P U) (clExtendIndices R' κ'.1) =
      clRegionalEpsilon G U (clExtendIndices R κ.1) := by
    have := eps_rigid P hRl (clExtendIndices R' κ'.1)
    rw [hF.erase_lower', hF.erase_lower] at this
    rw [hext]
    exact this
  have hk : cosetDecoration G L base (clExtendIndices R κ.1) =
      fun y => cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1) (naiveNodeEquiv G P y) := by
    funext y
    unfold cosetDecoration
    rw [hext]
  have hph : clRegionalPhase (unitTwistGarden G P) (twistedAtoms G P U) L γ δ
        (cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1)) (clLocalClock R' t (tEquivS P R R' τ)) =
      clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1)) (clLocalClock R t τ) := by
    have := phase_rigid P hRl L γ δ (cosetDecoration (unitTwistGarden G P) L base (clExtendIndices R' κ'.1))
      (clLocalClock R' t (tEquivS P R R' τ)) (clLocalClock R t τ)
      (fun v hv => hclock v (Finset.mem_of_mem_erase hv))
    rw [hF.erase_lower', hF.erase_lower] at this
    rw [hk]
    exact this
  have hst : clLocalStarProduct D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
        (clExtendIndices R' κ'.1) t (tEquivS P R R' τ) =
      clLocalStarProduct D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ := by
    rw [clLocalStarProduct_eq, clLocalStarProduct_eq]
    have := starProd_rigid P hB hR hG D D' L γ δ F layer hLayer layer' hLayer' base hC hT R (t 0)
      (clExtendIndices R' κ'.1) (clLocalClock R' t (tEquivS P R R' τ)) (clLocalClock R t τ)
      (fun v hv => hclock v hv)
    rw [hext]
    exact this
  have hdom := domain_iff_rigid hB hF R R' (fun v => layer (D.coreBranch hG v).toNode)
    (fun v => layer' (D'.coreBranch (unitTwistGarden_plain G P hG) v).toNode) hl t τ
  unfold clLocalSummand
  rw [heps]
  congr 1
  by_cases hm : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hdom.mpr hm)]
    rw [hph, hst]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hdom.mp h))]

include hB hF hC hT hl in
/-- **The weighted unit kernel is invariant under a rigid twist** (TARGET L1948, observation 1). -/
theorem clLocalKernelW_rigid (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    clLocalKernelW D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base W t0 t1 t2 e f g h =
      clLocalKernelW D hG R L γ δ F layer hLayer base W t0 t1 t2 e f g h := by
  unfold clLocalKernelW
  rw [order1_rigid P R R', zeta_rigid P R R' (hF.rigidAt b)]
  congr 1
  have hint : ∀ κ' : CLLocalDecoration R' L base ![e, f, g, h],
      ∫ τ' : CLInternalTime R', clLocalSummand D' (unitTwistGarden_plain G P hG) R' L γ δ F layer' hLayer' base
          ![e, f, g, h] ![t0, t1, t2] κ' τ' * W (clLocalClock R' ![t0, t1, t2] τ' (eB P b)) =
        ∫ τ : CLInternalTime R, clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![t0, t1, t2]
          (decEquivR hB hF R R' L base ![e, f, g, h] κ') τ * W (clLocalClock R ![t0, t1, t2] τ b) := by
    intro κ'
    rw [← (tEquivS_measurePreserving P R R').integral_comp' (g := fun τ' => clLocalSummand D' _ R' L γ δ F layer'
      hLayer' base ![e, f, g, h] ![t0, t1, t2] κ' τ' * W (clLocalClock R' ![t0, t1, t2] τ' (eB P b)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    show clLocalSummand D' _ R' L γ δ F layer' hLayer' base ![e, f, g, h] ![t0, t1, t2] κ' (tEquivS P R R' τ) *
        W (clLocalClock R' ![t0, t1, t2] (tEquivS P R R' τ) (eB P b)) = _
    rw [summand_rigid hB hF R R' hG D D' L γ δ F layer hLayer layer' hLayer' base ![e, f, g, h] hC hT hl,
      clockS_corr P R R' _ τ hB.2.2.1]
  rw [tsum_congr hint]
  exact (decEquivR hB hF R R' L base ![e, f, g, h]).tsum_eq
    (fun κ => ∫ τ : CLInternalTime R, clLocalSummand D hG R L γ δ F layer hLayer base ![e, f, g, h] ![t0, t1, t2]
      κ τ * W (clLocalClock R ![t0, t1, t2] τ b))

end Summand

section Congr
variable {d : ℕ} (R : CLRegionData G U a b) (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ)
  (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ clInteriorBranches R, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)

include hC hT hl in
/-- The weighted kernel reads the reconstruction data only through native rows and atom layers. -/
theorem clLocalKernelW_congr_data (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelW D1 hG R L γ δ F layer1 hLayer1 base W t0 t1 t2 e f g k =
      clLocalKernelW D2 hG R L γ δ F layer2 hLayer2 base W t0 t1 t2 e f g k := by
  unfold clLocalKernelW
  congr 1
  refine tsum_congr fun κ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  unfold clLocalSummand
  have hstar : ∀ (κ' : GNode G.tree → (Fin d → ℤ)) (t' : Fin 3 → ℝ) (τ' : CLInternalTime R),
      clLocalStarProduct D1 hG R L γ δ F layer1 hLayer1 base κ' t' τ' =
        clLocalStarProduct D2 hG R L γ δ F layer2 hLayer2 base κ' t' τ' :=
    fun κ' t' τ' => clLocalStarProduct_congr_data R hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base hC hT κ' t' τ'
  simp only [hstar]
  rw [clLocalTimeDomain_congr_data R hG D1 D2 layer1 layer2 hl]

end Congr

section LF
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- **Rigid invariance for a TRUE-choice LF construction at a placement that moves `U` rigidly.** -/
theorem clLocalKernelW_rigid_LF (h : LFConstruction s true) {U : Finset (GBranch s.skeleton.tree)}
    {a b : GBranch s.skeleton.tree} (hB : s.skeleton.molecule.IsBlock U a b) (hF : FullRigid s.placement U)
    (R : CLRegionData s.skeleton U a b)
    (R' : CLRegionData (unitTwistGarden s.skeleton s.placement) (twistedAtoms s.skeleton s.placement U)
      (eB s.placement a) (eB s.placement b))
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain true)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain true)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain true) layer' hLayer' = h.output)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelW h.data (s.chosen_plain true) R' L γ δ F layer' hLayer' base W t0 t1 t2 e f g k =
      clLocalKernelW s.data s.plain R L γ δ F layer hLayer base W t0 t1 t2 e f g k := by
  refine clLocalKernelW_rigid hB hF R R' s.plain s.data h.data L γ δ F layer hLayer layer' hLayer' base ?_ ?_ ?_
    W t0 t1 t2 e f g k
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hF.lower_notMem (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hF.lower_notMem (hq' ▸ hint)
    exact native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
  · intro v hv
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v (hF.ne_lower (Finset.mem_of_mem_erase hv))
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

/-- **Invariance for a FALSE-choice LF construction at a placement whose lower joint is outside `U`.** -/
theorem clLocalKernelW_false_LF (h : LFConstruction s false) {U : Finset (GBranch s.skeleton.tree)}
    {a b : GBranch s.skeleton.tree} (hlow : s.placement.lower ∉ U) (R : CLRegionData s.skeleton U a b)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernelW h.data (s.chosen_plain false) R L γ δ F layer' hLayer' base W t0 t1 t2 e f g k =
      clLocalKernelW s.data s.plain R L γ δ F layer hLayer base W t0 t1 t2 e f g k := by
  refine clLocalKernelW_congr_data R s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base ?_ ?_ ?_
    W t0 t1 t2 e f g k
  · intro q hq
    have hint := (mem_clRegionalPairs s.skeleton).mp hq
    have hne : q ≠ s.exceptional := by
      intro hqe
      have hqe' : q = pairOfLeaf s.skeleton s.plain s.placement.retained := hqe
      subst hqe'
      rcases pairOfLeaf_first_or_partner s.skeleton s.plain s.placement.retained with hq' | hq'
      · exact not_internal_retained_of s.placement hlow (hq' ▸ hint)
      · exact not_internal_pair_of s.placement hlow (hq' ▸ hint)
    have := native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hne
    have hp : s.pairs false q = q := pairOfLeaf_firstLeaf s.skeleton s.plain q
    rwa [hp] at this
  · intro v hv
    have hvl : v ≠ s.placement.lower := fun he => hlow (he ▸ Finset.mem_of_mem_erase hv)
    exact native_tree_eq h layer hLayer hspec layer' hLayer' hspec' v hvl
  · intro v _
    exact coreLayer_eq h layer hLayer hspec layer' hLayer' hspec' v

end LF

end WaveTurbulence.VineC
