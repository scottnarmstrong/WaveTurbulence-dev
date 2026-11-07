/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw10Final
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubiniInputs

/-! # The local kernel reads the reconstruction data only through native rows (V5 Step 4b, step 4)

`clLocalKernel_congr_data`: two reconstruction data `D1`, `D2` of the SAME skeleton whose native layered couples (at the
regional pairs of `U`), native layered trees (at the interior branches of `U`) and atom layers (at the interior branches)
agree give the same local kernel.  With `native_couple_eq`, `native_tree_eq`, `coreLayer_eq` this is the `K^T` invariance
for a FALSE-choice LF construction (no skeleton change, no label swap): `clLocalKernel_false_LF`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

section Congr
variable (R : CLRegionData G U a b) (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG U, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ clInteriorBranches R, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ clInteriorBranches R, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)

include hC hT in
theorem clLocalStarProduct_congr_data (κ : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (τ : CLInternalTime R) :
    clLocalStarProduct D1 hG R L γ δ F layer1 hLayer1 base κ t τ =
      clLocalStarProduct D2 hG R L γ δ F layer2 hLayer2 base κ t τ := by
  unfold clLocalStarProduct
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_) (Finset.prod_congr rfl fun v hv => ?_)
  · rw [hC p hp]
  · rw [hT v hv]

include hl in
theorem clLocalTimeDomain_congr_data (t : Fin 3 → ℝ) :
    clLocalTimeDomain R (fun v => layer1 (D1.coreBranch hG v).toNode) t =
      clLocalTimeDomain R (fun v => layer2 (D2.coreBranch hG v).toNode) t := by
  ext τ
  simp only [clLocalTimeDomain, Set.mem_ofPred_eq]
  refine and_congr (forall_congr' fun v => ?_) Iff.rfl
  rw [hl v.1 v.2]

include hC hT hl in
theorem clLocalKernel_congr_data (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernel D1 hG R L γ δ F layer1 hLayer1 base t0 t1 t2 e f g k =
      clLocalKernel D2 hG R L γ δ F layer2 hLayer2 base t0 t1 t2 e f g k := by
  unfold clLocalKernel
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

section False
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG) (h : LFConstruction s false)

/-- **`K^T` invariance for a FALSE-choice construction** (no skeleton change, no label swap): the kernel of the output
reconstruction at a CL block `T` whose upper joint is the lower joint of the placement is the kernel of the source. -/
theorem clLocalKernel_false_LF {T : Finset (GBranch s.skeleton.tree)} {z : GBranch s.skeleton.tree}
    (hB : s.skeleton.molecule.IsBlock T s.placement.lower z) (hCL : Mole.CLParentPattern s.skeleton T s.placement.lower z)
    (R : CLRegionData s.skeleton T s.placement.lower z)
    (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
    (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
    (layer' : GNode (h.data.forest (s.chosen_plain false)) → ℕ)
    (hLayer' : IsLayering (h.data.garden (s.chosen_plain false)) layer')
    (hspec' : layeredReconstruction h.data (s.chosen_plain false) layer' hLayer' = h.output)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    clLocalKernel h.data (s.chosen_plain false) R L γ δ F layer' hLayer' base t0 t1 t2 e f g k =
      clLocalKernel s.data s.plain R L γ δ F layer hLayer base t0 t1 t2 e f g k := by
  refine clLocalKernel_congr_data R s.plain h.data s.data L γ δ F layer' hLayer' layer hLayer base ?_ ?_ ?_ t0 t1 t2 e f g k
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

end False

/-! ## The S-part `spart` reads the data only through native rows -/

section SPart
variable {S : Finset (GBranch G.tree)} (hG : G.IsPlain) (D1 D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer1 : GNode (D1.forest hG) → ℕ) (hLayer1 : IsLayering (D1.garden hG) layer1)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  (hC : ∀ p ∈ clRegionalPairs hG S, nativeCoupleLayered D1 hG layer1 hLayer1 p = nativeCoupleLayered D2 hG layer2 hLayer2 p)
  (hT : ∀ v ∈ S.erase a, nativeChainLayered D1 hG layer1 hLayer1 v = nativeChainLayered D2 hG layer2 hLayer2 v)
  (hl : ∀ v ∈ S.erase a, layer1 (D1.coreBranch hG v).toNode = layer2 (D2.coreBranch hG v).toNode)

include hC hT in
theorem starProd_congr_data (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    starProd D1 hG L γ δ F layer1 hLayer1 base S a top x u = starProd D2 hG L γ δ F layer2 hLayer2 base S a top x u := by
  unfold starProd
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun p hp => ?_) (Finset.prod_congr rfl fun v hv => ?_)
  · rw [hC p hp]
  · rw [hT v hv]

include hC hT hl in
theorem spart_congr_data (b : GBranch G.tree) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    spart D1 hG L γ δ F layer1 hLayer1 base S a b x u = spart D2 hG L γ δ F layer2 hLayer2 base S a b x u := by
  unfold spart
  have hdom : DomS (fun v => layer1 (D1.coreBranch hG v).toNode) S a u ↔
      DomS (fun v => layer2 (D2.coreBranch hG v).toNode) S a u := by
    unfold DomS
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    simp only []
    rw [hl v hv]
  have hstar := starProd_congr_data hG D1 D2 L γ δ F layer1 hLayer1 layer2 hLayer2 base hC hT (u a) x u
  rw [hstar]
  by_cases hd : DomS (fun v => layer1 (D1.coreBranch hG v).toNode) S a u
  · simp [hd, hdom.mp hd]
  · have hd' : ¬ DomS (fun v => layer2 (D2.coreBranch hG v).toNode) S a u := fun h => hd (hdom.mpr h)
    simp [hd, hd']

end SPart

end WaveTurbulence.VineEstS4
