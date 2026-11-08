/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.RedL
public import WaveTurbulence.Foundations.Flower.MkUnits.WMember

/-! # MK-UNITS-L (B3-2): the weighted member identity with per-unit top filters

* `skelValW_slotFWW`, `valueSelW_modesWL`: Stage1WVine's `skelVal_slotFW`, `valueSelW_modesW` with the units' top
  weights: the value of a reconstruction with the decoration weight `fwWeight · topWt(collapse κ)` is the outer mode sum
  with the generic unit factors `unitKernelMGW (slotFWW … Wt)`.
* `member_ker_eqWMkL`, `memberRBMkL`, `member_hVWMkL`, `member_integWMkL`, `member_hsmWMkL`: B3's run-class member
  identity (`MkUnits/WMember`) with the extra weight `E`, presented on the member by the unit top filters `SU`: the
  member's unit kernels are V5W-2L's `unitRecenteredFWL p (g j₁) (SU j) y (y.2 j) …`.

Adapted from `Flower/Stage1WVine/WMember1.lean` and `Flower/MkUnits/WMember.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.V5W2L (topFilterWeightL unitRecenteredFWL)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-! ## The top weights at a skeleton decoration -/

section TopWt
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

/-- The product of the top weights `Wt` at the unit tops. -/
def topWt (blk : J → CLBlock S) (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (x : GNode S.tree → (Fin d → ℤ)) : ℂ :=
  ∏ j, nodeWeight (Wt (blk j).upper) L base (blk j).upper x

theorem norm_topWt_le (blk : J → CLBlock S) (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ)
    (hWt : ∀ v q, ‖Wt v q‖ ≤ 1) (L : ℝ) (base : Mom d) (x : GNode S.tree → (Fin d → ℤ)) :
    ‖topWt blk Wt L base x‖ ≤ 1 := by
  unfold topWt
  refine (Finset.norm_prod_le _ _).trans ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => hWt _ _

theorem topW_slotFWW (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (gT : Fin w → Mom d → ℂ)
    (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ) (L' : ℝ) (base : Mom d) (x : GNode S.tree → (Fin d → ℤ)) :
    topW blk (slotFWW D hS layer hLayer L γ δ h p gT Wt) L' base x = topWt blk Wt L' base x := by
  unfold topW topWt slotFWW
  rfl

end TopWt

/-! ## The weighted value of a reconstruction in mode form -/

theorem skelValW_slotFWW {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] (blk : J → CLBlock S)
    (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (selSk : GenDecoration S d roots 0 → Prop)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (g : Fin w → Mom d → ℂ)
    (Wt : GBranch S.tree → (Fin 4 → Mom d) → ℂ) :
    skelValW blk D hS L γ δ base roots tt layer selSk (slotFWW D hS layer hLayer L γ δ h p g Wt) =
      (coupling d L γ δ : ℂ) ^ S.order * S.zeta *
        ∑' κ : GenDecoration S d roots 0, if selSk κ then (epsDec S κ.1 : ℂ) * ∫ τ : GBranch S.tree → ℝ,
          (coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt).indicator
            (fun τ => phaseProd L γ δ S (cosetDecoration S L base κ.1) τ *
              (Stage1WNoVine.reducedStarProductLeavesNW D hS L γ δ
                (typeProfiles (layeredReconstruction D hS layer hLayer) h)
                (Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ *
                topWt blk Wt L base κ.1)) τ
          else 0 := by
  unfold skelValW skelTermW
  congr 2
  funext κ
  have key : ∀ τ : GBranch S.tree → ℝ, (∏ s, (slotFWW D hS layer hLayer L γ δ h p g Wt).fs s (slotTs hS tt τ s)
      (base + latticePoint L (κ.1 (slotNode hS s)))) =
      Stage1WNoVine.reducedStarProductLeavesNW D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h)
        (Stage1WNoVine.fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer tt base κ.1 τ :=
    fun τ => Stage1WNoVine.prod_slotFnNW D hS L γ δ _ _ layer hLayer tt base κ.1 τ
  simp only [key, topW_slotFWW]

/-- **The weighted value of a reconstruction with the units' top weights in mode form** (Stage1WVine's
`valueSelW_modesW`). -/
theorem valueSelW_modesWL {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R)) {S : Garden (2 * R)} {J : Type}
    [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden (2 * R)} (Φ : SpliceShape blk Gsb)
    (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (hctrl : U.toLF.Controlled (layeredReconstruction D hS layer hLayer)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration S P.d roots 0 → Prop) (Zw : GenDecoration Gsb P.d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S P.d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (Wt : GBranch S.tree → (Fin 4 → Mom P.d) → ℂ) (hWt : ∀ v q, ‖Wt v q‖ ≤ 1)
    (RB : ∀ i, RegBoundW blk hS (slotFWW D hS layer hLayer P.L P.γ P.δ (U.h i) p g Wt) P.L base)
    (fam : U.ι → SlotFam Gsb P.d) (Box : U.ι → ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ i s', ∀ ts ∈ Box i s', ∀ x, HasSum
      (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
      (slotFW D hS layer hLayer P.L P.γ P.δ (U.h i) p g (Φ.iota hS hSb s') ts x))
    (hbox : ∀ i, ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box i s') :
    valueSelW U.toLF tt base roots (layeredReconstruction D hS layer hLayer)
        (fun κ => selSk (collapseGenDecoration D hS κ))
        (fun κ => fwWeight p g base (layeredReconstruction D hS layer hLayer) κ *
          topWt blk Wt P.L base (collapseGenDecoration D hS κ).1) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
            (unitKernelMGW blk D hS (slotFWW D hS layer hLayer P.L P.γ P.δ (U.h i) p g Wt) P.L P.γ P.δ layer base)) ∧
    ∀ i, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM Gsb P.L P.γ P.δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode)
            (Φ.hinges hd) Zw hSb (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
            (unitKernelMGW blk D hS (slotFWW D hS layer hLayer P.L P.γ P.δ (U.h i) p g Wt) P.L P.γ P.δ layer base)) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  refine ⟨?_, fun i => (hasSum_skelVal_outerValMGW Φ (RB i) hd hSb hL0 P.γ P.δ D layer tt selSk Zw hZ (fam i)
    (Box i) (hexp i) (hbox i)).summable⟩
  rw [valueSelW_skeleton_reductionM U.toLF D hS layer hLayer hctrl hd1 hL1 tt base roots selSk p g cψ
    hc hg (fun κ => topWt blk Wt P.L base κ.1) 1 (fun κ => norm_topWt_le blk Wt hWt P.L base κ.1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have := (hasSum_skelVal_outerValMGW Φ (RB i) hd hSb hL0 P.γ P.δ D layer tt selSk Zw hZ (fam i) (Box i) (hexp i)
    (hbox i)).tsum_eq
  rw [this, skelValW_slotFWW]
  rfl

/-! ## The member identity of a run class with per-unit top filters -/

variable {p : ℕ} {kind : Bool}

/-- The top weight of a run-class member: `topFilterWeightL (SU j)` at the top of its unit `j`. -/
abbrev memberTopW {R d : ℕ} {a : PrescribedPrimeGarden (2 * R)} {mk : Stage1Mk.MarkFn (2 * R)}
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)))
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) :
    GBranch y.1.skeleton.tree → (Fin 4 → Mom d) → ℂ :=
  topWeightOf (fun j => (y.2 j).blk.a) SU

theorem memberTopW_apply {R d : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) (j) :
    memberTopW (d := d) y SU (y.2 j).blk.a = topFilterWeightL (SU j) :=
  topWeightOf_apply (top := fun j => (y.2 j).blk.a) (upper_injective (source_disjMk a mk y hy)) SU j

/-- For a run-class member, the generic unit factor of the weighted slot family with the member's top filters is
V5W-2L's pinned `unitRecenteredFWL` (B3's `member_ker_eqWMk` with `SU`). -/
theorem member_ker_eqWMkL {R d : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (L γ δ : ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (base : Mom d) (g : Fin (2 * R) → Mom d → ℂ)
    (hcan : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) :
    unitKernelMGW (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain
        (slotFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ h p g (memberTopW y SU))
        L γ δ (stateLayer y.1) base =
      fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ) (t : Fin 3 → ℝ)
          (k : Fin 4 → Mom d) =>
        unitRecenteredFWL p
          (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
          y.1 (y.2 j) L γ δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) base
          (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
  funext j lam t k
  rw [unitKernelMG_slotFWW_eq y.1 y.2 (stateLayer y.1) (stateLayer_isLayering y.1) (stateLayer_spec y.1) L γ δ h p g
    base hcan hlay (memberTopW y SU) SU (fun j => memberTopW_apply a mk y hy SU j) j lam t k]
  have hidx := source_upper_tree_indexMk a mk y hy j
  have h1 : unitProfile (fun j => unitClBlock (y.2 j)) h j =
      unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j := by
    funext q
    unfold unitProfile
    exact congrArg₂ (fun u v => h q u v) hidx hidx
  have h2 : g (y.2 j).blk.a.1.1 =
      g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1 :=
    congrArg g hidx
  rw [h1, h2]

/-- The regional bound of a member's weighted slot family with top filters (at a marking). -/
def memberRBMkL {R : ℕ} {P : WTParams} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d)
    (hL1 : 1 ≤ P.L) (base : Mom P.d) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) (i : U.ι) :
    RegBoundW (fun j => unitClBlock (y.2 j)) y.1.plain
      (slotFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
        (memberTopW y SU)) P.L base :=
  regBoundFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
    (fun j => unitClBlock (y.2 j)) cψ hc hg base (lt_of_lt_of_le zero_lt_one hL1).ne'
    (fun j => hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p
      (NNReal.coe_nonneg (U.b i)) hlay (fun q j j' hq => hB i q j j' hq) j)
    (memberTopW y SU) (norm_topWeightOf_le _ SU)

/-- **The weighted member identity with per-unit top filters** (B3's `member_hVWMk` with the extra weight `E`
presented on the member by `SU`). -/
theorem member_hVWMkL {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
    (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (π : PcA R p kind A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
    (hout : a.outputs (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mkF) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (htt : ∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (fam : U.ι → SlotFam (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d)
    (hexpR : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
      ∀ x, HasSum
        (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
        (slotFW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L P.γ P.δ (U.h i) p g
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
          ts x))
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ)
    (E : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hE : ∀ κ : GenDecoration (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
        (stateLayer_isLayering y.1)).garden P.d roots 0,
      E _ κ = ∏ j, nodeWeight (topFilterWeightL (SU j)) P.L base (y.2 j).blk.a
        (collapseGenDecoration y.1.data y.1.plain κ).1)
    (hctrl : U.toLF.Controlled y.1.layered) :
    (valueSelW U.toLF tt base roots y.1.layered (selPMk p kind A P base roots mkF π y.1.layered)
        (fun κ => fwWeight p g base y.1.layered κ * E y.1.layered κ) =
      @Finset.sum U.ι ℂ _ (@Finset.univ _ U.fin) (fun i =>
        ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
            (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
            (fun z => if selSkCMk a mk P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            (fun j lam t k => unitRecenteredFWL p
              (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
              y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))))
    ∧ ∀ i : U.ι, Summable (fun ξ : (∀ s, (fam i).Λ s) => ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
            (a.normalizedPiece 0 (mk a.prime)).layer (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges
            (fun z => if selSkCMk a mk P.L P.γ P.η (by positivity) base roots z then 1 else 0) hG
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
              (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
            (fun j lam t k => unitRecenteredFWL p
              (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
              y.1 (y.2 j) P.L P.γ P.δ
              (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
              base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3))) := by
  obtain ⟨M, hr, hn, hsh⟩ := memShape_data a mk y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hrel : PrescribedPrimeGarden.Related (p := p) (kind := kind) (repPt π) (memberPointMk a mk y M hr) mkF :=
    hπ ▸ memberPoint_relatedMk hFT a hout y hy M hr
  have hsel : selPMk p kind A P base roots mkF π y.1.layered = fun κ => selAt P base
      ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩
      (transportGroupPrescription (batchMolIso hr.batch) a.sigma) κ :=
    funext fun κ => propext (selPMk_iff_related P base roots π (memberPointMk a mk y M hr) hrel y.1.layered rfl κ)
  rw [hsel, valueSelW_selAt_reconstruction U.toLF y.1.data (VineA.batch_prime hr.batch a.prime.prime)
    (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered (stateLayer_spec y.1) y.1.decodes
    (transportGroupPrescription (batchMolIso hr.batch) a.sigma) tt base roots
    (fun LG κ => fwWeight p g base LG κ * E LG κ)]
  have hw : (fun κ => fwWeight p g base
        (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) κ *
        E (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) κ) =
      fun κ => fwWeight p g base
        (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) κ *
        topWt (fun j => unitClBlock (y.2 j)) (memberTopW y SU) P.L base
          (collapseGenDecoration y.1.data y.1.plain κ).1 := by
    funext κ
    show _ * E _ κ = _
    rw [hE κ]
    unfold topWt
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    show _ = nodeWeight (memberTopW y SU (y.2 j).blk.a) P.L base (y.2 j).blk.a _
    rw [memberTopW_apply a mk y hy SU j]
  rw [hw]
  have hZ : ∀ κ : GenDecoration y.1.skeleton P.d roots 0,
      (if NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1
        then (1 : ℝ) else 0) =
      (fun z => if selSkCMk a mk P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0)
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) := by
    intro κ
    rw [hsh]
    exact (hZ_commonMk a mk hr hn (markTransported_imageMark _ (mk a.prime)) (gapValueSelDartsMk_all (2 * R)) hL0
      P.γ P.η base roots κ).trans
      (selSkCMk_ite a mk P.L P.γ P.η hL0 base roots _)
  have hctrl' : U.toLF.Controlled (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)) := by
    rw [stateLayer_spec y.1]; exact hctrl
  have hexp : ∀ i s', ∀ ts ∈ slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'),
      ∀ x, HasSum
        (fun l => ((fam i).w s' l : ℂ) * (fam i).a s' l x * fsPhase ((fam i).m s' l) ts)
        (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
          ((memShape a mk y hy).iota y.1.plain hG s') ts x) := by
    intro i s' ts hts x
    rw [memShape_slotFW a mk y hy hG (U.h i) P.L P.γ P.δ p g s']
    exact hexpR i s' ts hts x
  have key := valueSelW_modesWL U (memShape a mk y hy) (source_disjMk a mk y hy) y.1.data y.1.plain hG
    (stateLayer y.1) (stateLayer_isLayering y.1) hctrl' hd1 hL1 tt base roots
    (fun κ => NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1)
    (fun z => if selSkCMk a mk P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hZ p g cψ hc hg
    (memberTopW y SU) (norm_topWeightOf_le _ SU)
    (memberRBMkL a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg SU) fam
    (fun i s' => slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'))
    hexp (fun i τ hτ s' => memShape_hbox a mk y hy hG tt htt τ hτ s')
  refine ⟨?_, fun i => ?_⟩
  · rw [key.1, memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
      memShape_hclk a mk y hy, memShape_hmom a mk y hy]
    simp only [member_ker_eqWMkL a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)]
  · have h := key.2 i
    rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
      memShape_hclk a mk y hy, memShape_hmom a mk y hy] at h
    simp only [member_ker_eqWMkL a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
    exact h

/-- The integrability hypothesis of list-T4 for a member at a marking (B3's `member_integWMk` with `SU`). -/
theorem member_integWMkL {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (amp : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Mom P.d → ℂ)
    (frq : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Fin 2 → ℤ)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (i : U.ι)
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) :
    Integrable (outerIntegrandM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
      (a.normalizedPiece 0 (mk a.prime)).layer hG amp frq
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      (fun j lam t k => unitRecenteredFWL p
        (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
        y.1 (y.2 j) P.L P.γ P.δ
        (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
        base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) := by
  have h := integrable_outerIntegrandMGW (memShape a mk y hy)
    (memberRBMkL a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg SU i)
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq z
  rw [memShape_lay_eq a mk y hy, memShape_route a mk y hy hG, memShape_hclk a mk y hy,
    memShape_hmom a mk y hy] at h
  simp only [member_ker_eqWMkL a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

/-- The decoration-summability hypothesis of list-T4 for a member at a marking (B3's `member_hsmWMk` with `SU`). -/
theorem member_hsmWMkL {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (P : WTParams)
    (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (hlay : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → ∀ x, stateLayer y.1 x ≤ p)
    (hcanM : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)),
      y ∈ sourceClass a p kind mk → IsCanonGC (p + 1) y.1.layered)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (amp : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Mom P.d → ℂ)
    (frq : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G → Fin 2 → ℤ)
    (hsum : Summable fun z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 =>
      ampBound hG P.L base amp z)
    (Zw : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 → ℝ) (hZw : ∀ z, |Zw z| ≤ 1)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (i : U.ι) :
    Summable (fun z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0 =>
      (splicedEpsilon (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G
          (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges z.1 : ℂ) * (Zw z : ℂ) *
        ∫ τ, outerIntegrandM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
          (a.normalizedPiece 0 (mk a.prime)).layer hG amp frq
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
            (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
          (fun j lam t k => unitRecenteredFWL p
            (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
            y.1 (y.2 j) P.L P.γ P.δ
            (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
            base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ) := by
  have h := summable_outer_decorationsGW (memShape a mk y hy)
    (memberRBMkL a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg SU i)
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq Zw hZw hsum
  rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy] at h
  simp only [member_ker_eqWMkL a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

end WaveTurbulence.Flower.MkUnitsL
