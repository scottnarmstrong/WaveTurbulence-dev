/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WClass
public import WaveTurbulence.Foundations.Flower.MkUnits.UnitGap
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WHinge2

/-! # MK-UNITS: the hinge data of the weighted units at a marking

Stage1WVine's `unit_hinge_dataW` (main's `unit_hinge_data` on the on-chain route `hinge_units_const →
exists_hinge_data_mod_ck_w`, uclock Rev. 1 U-F6, through Stage1WVine's generic `hinge_units_constW`) for the run
assembly `sourceAssemblyMk a mk` of the representative:
* G1 (time box): main's `g1_unitsMk`, `qOut_one_eq_layMk`, `qOut_two_eq_layMk`, `hqle_unitsMk`;
* G2 (`outSet`): `mem_outSet_of_gsbNMk` (`UnitGap`, the runs' gap from the σ-restriction);
* leaf independence: main's `unit_hleaf1`/`unit_hleaf2` at a marking (`unit_hleaf1Mk`, `unit_hleaf2Mk`), through the
  common shape of the lifted batch with the image marking.

Adapted from `Flower/Stage1WVine/WHinge2.lean` and main's `Stage1/Represents/RepVD4.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS5C
  VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine

/-! ## Leaf independence of the unit class kernels at a marking -/

section Local
variable {w : ℕ} {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S) (Mk : Set (CLVine S))
  (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem unit_hleaf_auxMk (hp : IsPrimeGarden S) {p : ℕ} {kind : Bool} (j : Fin (unitBlocks S σ Mk).length)
    (k : Fin 4) (r : Fin w)
    (hflag : nodeClk (stSt S σ Mk).G ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j k) = Sum.inl r)
    (x : Σ X : FamilyReconstruction w (assemblySourceFamily (alignedAssemblyMk hM σ Mk j)).CoreIndex,
      ChainAt X.skeleton X.family)
    (hx : x ∈ canonFinsetK p kind (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j))) :
    (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.2 ∉
      (x.1.skeleton.tree
        (bnodes (⟨x.2.U, x.2.a, x.2.b, x.2.block, x.2.cl⟩ : CLBlock x.1.skeleton) k).1.1).branching := by
  obtain ⟨X, c⟩ := x
  obtain ⟨N, hN, hR⟩ := (mem_canonFinsetK hp).mp hx
  obtain ⟨Z, hZb, hZe⟩ := batch_lift (e := (unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)
    ((unitsSplit (alignedAssemblyMk hM σ Mk)).inj j) hR.batch
    (X := unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer) rfl
  obtain ⟨vs, hRZ⟩ := batch_reachU (Qm := (unitsSplit (alignedAssemblyMk hM σ Mk)).Q) hZb
    (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk))
  have hN' : N.Nodup := perm_univ_nodup hN
  have hproj := ReachU.proj (e := (unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)
    (he := (unitsSplit (alignedAssemblyMk hM σ Mk)).inj j) j ((unitsSplit (alignedAssemblyMk hM σ Mk)).q_emb j) N hRZ
  subst hZe
  have hc := Reach.region_unique hN' hN' hR hproj
  subst hc
  have hn : (N.map ((unitsSplit (alignedAssemblyMk hM σ Mk)).emb j)).Nodup :=
    hN'.map ((unitsSplit (alignedAssemblyMk hM σ Mk)).inj j)
  have hm := congrFun (congrFun (commonShape_hmomMk hM σ D hS layer hLayer hRZ hn
    (markTransported_imageMark _ Mk)) j) k
  refine not_branch_of_nodeClk_inl_shape (commonShapeMk hM σ D hS layer hLayer hRZ hn
    (markTransported_imageMark _ Mk)) (member_disjMk hM σ D hS layer hLayer hRZ hn) j k r ?_
  rw [hm]
  exact hflag

theorem unit_hleaf1Mk (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ Mk).length)
    (h1 : leafFlag hM σ j 1) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).positive).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_oneMk hM σ j).mp h1
  exact unit_hleaf_auxMk hM σ Mk D hS layer hLayer hp j 2 r hr x hx

theorem unit_hleaf2Mk (hp : IsPrimeGarden S) {p : ℕ} (j : Fin (unitBlocks S σ Mk).length)
    (h2 : leafFlag hM σ j 2) :
    ∀ x ∈ canonFinsetK p (objKind w) (startState (alignedAssemblyMk hM σ Mk j) D hS layer hLayer)
      (chainStart (alignedAssemblyMk hM σ Mk j)),
      (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.2 ∉
        (x.1.skeleton.tree (x.2.b.child (clRegionData x.1.skeleton x.2.block x.2.cl).negative).1.1).branching := by
  intro x hx
  obtain ⟨r, hr⟩ := (leafFlag_twoMk hM σ j).mp h2
  exact unit_hleaf_auxMk hM σ Mk D hS layer hLayer hp j 3 r hr x hx

end Local

/-! ## The hinge data -/

open scoped Classical in
/-- **The hinge data of the weighted units of the representative at a marking** (Stage1WVine's
`unit_hinge_dataW`). -/
theorem unit_hinge_dataWMk (P : WTParams) (hV : V5FrontierClassBoundAt P) (hM9 : VINEPARAM)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd1 : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η)
    (hη2 : P.η ≤ 1 / 2) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL1 : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (hcan : IsCanonGC (p + 1) a.layered)
    (hord : (a.prime.data.garden a.prime.prime.1).order ≤ P.N (p + 1) ^ 4)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ)
    (hre : ∀ j x, (g j x).im = 0)
    (hp' : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (bb : ℝ) (hbb : 0 ≤ bb)
    (hB : ∀ q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (hp' q j j') ≤ ENNReal.ofReal bb)
    (lam : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℤ) :
    ∃ (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) P.d)
      (Mh : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkProp (a.normalizedPiece P.d (mk a.prime)) tt base roots
        (selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots)
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
          (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
        (fun j => unitHkFW P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) hp' j) base
          (lam j)) H ∧
      ∏ j, Mh j = ChinFW P.d P.η ^ Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) *
        (∏ j, unitMassFW P hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ bb) *
        ∏ j, (1 + |((lam j : ℤ) : ℝ)|) ^ (6 * P.η ^ 6) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hspec := (hinge_units_constW P.d P.η hη0.le).choose_spec
  have hChin : ChinFW P.d P.η = (hinge_units_constW P.d P.η hη0.le).choose := by
    unfold ChinFW; rw [dif_pos hη0.le]
  rw [hChin]
  have hcan' : IsCanonGC (p + 1) (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) := by rw [sourceLayer_reconstructs]; exact hcan
  have hordS : a.prime.skeleton.order ≤ P.N (p + 1) ^ 4 := by
    have := a.prime.data.decoded_order a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)
    omega
  have hcl : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length,
      clLocalOrder1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j)) ≤ P.N 1 ^ 4 := fun j =>
    clLocalOrder1_le_N1 P _ hordS
  have hh' : ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length, ∀ r ≤ p,
      SNormR (40 * P.d) (40 * P.d) (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j r) ≤
        ENNReal.ofReal bb :=
    fun j r hr => hB r _ _ hr
  have hLay : (a.normalizedPiece P.d (mk a.prime)).layer = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)) := by
    funext c
    show RegRed.coreLayer a.layered a.prime.data a.prime.prime.1 a.prime.decodes
      ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).M.ob c) = _
    rw [coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
      (sourceLayer_reconstructs a) a.prime.decodes]
    exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ rfl _ _).symm
  have hG1 := g1_unitsMk P hMa a.totalSigma hM9 (Mk := mk a.prime) (B₀ := sourceAssemblyMk a mk) a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) base tt roots
    (selSkCMk a mk P.L P.γ P.η hL0.ne' base roots)
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
      (fun i => latPt P.d (c i)))
    (fun j c hc => qOut_one_eq_layMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j c hc => qOut_two_eq_layMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) c hc)
    (fun j => hqle_unitsMk hMa a.totalSigma j a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a))
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      NormalizedSplice.gapSpecificationMk a.prime.skeleton a.totalSigma (mk a.prime), fun _ => 0, fun _ => 0⟩
  have hG2 : ∀ κ : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0,
      selSkCMk a mk P.L P.γ P.η hL0.ne' base roots κ →
      ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (c : Fin 4 → Fin P.d → ℤ),
      (∀ i, ‖(base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma (mk a.prime)).hmom
          (unitBlkMk_disj hMa a.totalSigma (mk a.prime)) j i))) - latPt P.d (c i)‖ ≤ 1) →
        sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
            (fun i => base + latticePoint P.L (κ.1 ((stShape hMa a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj hMa a.totalSigma (mk a.prime)) j i))) ∈
          outSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
              (fun i => latPt P.d (c i))) base) P.L P.γ P.η := by
    intro κ hκ j c hball
    refine mem_outSet_of_gsbNMk hMa a.prime.prime.1 a.totalSigma hL0.ne' P.γ P.η base roots κ D' rfl ?_ j c hball _
      rfl rfl
    have h1 := NormalizedSplice.gapValue_eq_indicatorMk a.totalSigma D' rfl P.L P.γ P.η base κ.1
    rw [← h1]
    rw [show NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) P.L P.γ P.η base κ.1 = 1 from hκ]
    exact one_ne_zero
  have hcont : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length)
      (c : Fin 4 → Fin P.d → ℤ) (lam : ℤ),
      ∀ E ∈ outSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)
        (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
          (fun i => latPt P.d (c i))) base) P.L P.γ P.η,
        ContinuousOn (fun t => unitHkFW P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) g (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t
          (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode) E))
          (cubeSet (unitD hM9 (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a)
            (sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
              (fun i => latPt P.d (c i))) base).qOut) :=
    fun j c lam => unit_hcontW hgate hinc htop hd1 hη0 hη6 hη2 hC1 hδ hL1 hw hp
      (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) bb (hh' j) a.prime.prime hM9
      (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord g cψ
      hc hgp hre _ base lam
  have hind : ∀ (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ)
      (t t' : Fin 3 → ℝ) (k : Fin 4 → Mom P.d), (∀ i, ¬ leafFlag hMa a.totalSigma j i → t i = t' i) →
      unitHkFW P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t k =
      unitHkFW P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) g
        (unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) base lam t' k :=
    fun j lam t t' k ht => unitHkFW_hind P p (sourceAssemblyMk a mk j) a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) g _ base (leafFlag hMa a.totalSigma j) (leafFlag_zeroMk hMa a.totalSigma j)
      (unit_hleaf1Mk hMa a.totalSigma (mk a.prime) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) a.prime.prime j)
      (unit_hleaf2Mk hMa a.totalSigma (mk a.prime) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) a.prime.prime j) lam t t' k ht
  obtain ⟨H, Mh, hsum, hHk, hprod⟩ := hspec.2 P rfl rfl hV (by linarith) hL0 hp a.prime.prime hM9 a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) hcan' hord (B₀ := sourceAssemblyMk a mk) hcl g cψ hc
    hgp hre (fun j => unitProfile (unitBlkMk hMa a.totalSigma (mk a.prime)) hp' j) (fun _ => bb) (fun _ => hbb) hh'
    (fun j c => sumintBoundary (a.prime.skeleton.sign (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper.toNode)
      (fun i => latPt P.d (c i))) base (fun j => hqle_unitsMk hMa a.totalSigma j a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a)) hcont (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G tt roots
    (selSkCMk a mk P.L P.γ P.η hL0.ne' base roots)
    ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).layer
      (RegRed.coreLayer (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a))
        a.prime.data a.prime.prime.1 (a.prime.data.garden_decodes a.prime.prime.1)))
    ((stShape hMa a.totalSigma (mk a.prime)).hmom (unitBlkMk_disj hMa a.totalSigma (mk a.prime)))
    ((stShape hMa a.totalSigma (mk a.prime)).hclk (unitBlkMk_disj hMa a.totalSigma (mk a.prime)))
    (leafFlag hMa a.totalSigma)
    (fun j i => ((qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlkMk hMa a.totalSigma (mk a.prime) j).upper
      (unitBlkMk hMa a.totalSigma (mk a.prime) j).lower (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j)) i : ℕ) :
        ℝ)) hind hG1 hG2 lam
  refine ⟨H, Mh, hsum, ?_, hprod⟩
  intro κ hκ τ hτ j c hball
  rw [hLay] at hτ
  exact hHk κ hκ τ hτ j c hball

end WaveTurbulence.Flower.MkUnits
