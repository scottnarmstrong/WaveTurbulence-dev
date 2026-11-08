/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.WAlign
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WMember2
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK5

/-! # MK-UNITS: the weighted member identity of a run class at a marking

Stage1WVine's `member_ker_eqW`, `memberRB`, `member_hVW`, `member_integW`, `member_hsmW` (main's VINE-B♯ member identity
with the frontier weight) for a member `y` of the run class `sourceClass a p kind mk`: its weighted value is the outer
mode sum of the representative's spliced garden at the marking, with the member's pinned unit kernels
`unitRecenteredFW`.  The gap selection uses B2c's `gapValue_eq_selDartsMk` (through main's `hZ_commonMk`), the
member's prescribed point uses `memberPoint_relatedMk`/`selPMk_iff_related` (`Code`).

Adapted from `Flower/Stage1WVine/WMember1.lean`, `WMember2.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.Flower.Stage1WVine

variable {p : ℕ} {kind : Bool}

/-- B2c's dart-label gap identity at every garden, prescription and marking (B1b-3's hypothesis form). -/
theorem gapValueSelDartsMk_all (w : ℕ) : GapValueSelDartsMk w :=
  fun H τ _ _ L γ η base c κ hκ hc0 zsb hlab =>
    NormalizedSplice.gapValue_eq_selDartsMk (Mole.garden_isMolecule H) τ L γ η base c κ hκ hc0 zsb hlab

/-- For a run-class member, VINE-B♯'s unit factor of the weighted slot family is the pinned `unitRecenteredFW` with
the common unit weight (Stage1WVine's `member_ker_eqW` at a marking). -/
theorem member_ker_eqWMk {R d : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (L γ δ : ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (base : Mom d) (g : Fin (2 * R) → Mom d → ℂ)
    (hcan : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p) :
    unitKernelMG (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain
        (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ h p g) L γ δ (stateLayer y.1)
        base =
      fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ) (t : Fin 3 → ℝ)
          (k : Fin 4 → Mom d) =>
        unitRecenteredFW p
          (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) none
          y.1 (y.2 j) L γ δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) base
          (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
  funext j lam t k
  rw [unitKernelMG_slotFW_eq y.1 y.2 (stateLayer y.1) (stateLayer_isLayering y.1) (stateLayer_spec y.1) L γ δ h p g
    base hcan hlay j lam t k]
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

/-- The regional bound of a member's weighted slot family (at a marking). -/
def memberRBMk {R : ℕ} {P : WTParams} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (U : TypeFamily P (2 * R)) (hd1 : 1 ≤ P.d)
    (hL1 : 1 ≤ P.L) (base : Mom P.d) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (hB : ∀ i q j j', q ≤ p → SNormR (40 * P.d) (40 * P.d) (U.h i q j j') ≤ ENNReal.ofReal (U.b i : ℝ))
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (i : U.ι) :
    RegBound (fun j => unitClBlock (y.2 j)) y.1.plain
      (slotFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g) P.L base :=
  regBoundFW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ (U.h i) p g
    (fun j => unitClBlock (y.2 j)) cψ hc hg base (lt_of_lt_of_le zero_lt_one hL1).ne'
    (fun j => hF_unit_of_bounded y.1.data y.1.plain hL1 hd1 (U.h i) (stateLayer y.1) base p
      (NNReal.coe_nonneg (U.b i)) hlay (fun q j j' hq => hB i q j j' hq) j)

open scoped Classical in
/-- **The weighted member identity at a marking** (Stage1WVine's `member_hVW`). -/
theorem member_hVWMk {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
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
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hctrl : U.toLF.Controlled y.1.layered) :
    (valueSelW U.toLF tt base roots y.1.layered (selPMk p kind A P base roots mkF π y.1.layered)
        (fwWeight p g base y.1.layered) =
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
            (fun j lam t k => unitRecenteredFW p
              (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) none
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
            (fun j lam t k => unitRecenteredFW p
              (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) none
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
    (transportGroupPrescription (batchMolIso hr.batch) a.sigma) tt base roots (fwWeight p g base)]
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
  have key := valueSelW_modesW U (memShape a mk y hy) (source_disjMk a mk y hy) y.1.data y.1.plain hG
    (stateLayer y.1) (stateLayer_isLayering y.1) hctrl' hd1 hL1 tt base roots
    (fun κ => NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) P.L P.γ P.η base κ.1)
    (fun z => if selSkCMk a mk P.L P.γ P.η hL0 base roots z then (1 : ℝ) else 0) hZ p g cψ hc hg
    (memberRBMk a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg) fam
    (fun i s' => slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s'))
    hexp (fun i τ hτ s' => memShape_hbox a mk y hy hG tt htt τ hτ s')
  refine ⟨?_, fun i => ?_⟩
  · rw [key.1, memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
      memShape_hclk a mk y hy, memShape_hmom a mk y hy]
    simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)]
  · have h := key.2 i
    rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
      memShape_hclk a mk y hy, memShape_hmom a mk y hy] at h
    simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
    exact h

/-- The integrability hypothesis of T4 for a member at a marking (Stage1WVine's `member_integW`). -/
theorem member_integWMk {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (P : WTParams)
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
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (i : U.ι)
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.d roots 0) :
    Integrable (outerIntegrandM (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L P.γ P.δ base roots tt
      (a.normalizedPiece 0 (mk a.prime)).layer hG amp frq
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG)
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)))
      (fun j lam t k => unitRecenteredFW p
        (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) none
        y.1 (y.2 j) P.L P.γ P.δ
        (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
        base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z) := by
  have h := integrable_outerIntegrandMG (memShape a mk y hy)
    (memberRBMk a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg i)
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq z
  rw [memShape_lay_eq a mk y hy, memShape_route a mk y hy hG, memShape_hclk a mk y hy,
    memShape_hmom a mk y hy] at h
  simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

/-- The decoration-summability hypothesis of T4 for a member at a marking (Stage1WVine's `member_hsmW`). -/
theorem member_hsmWMk {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (P : WTParams)
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
          (fun j lam t k => unitRecenteredFW p
            (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) none
            y.1 (y.2 j) P.L P.γ P.δ
            (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) (U.h i) j)
            base (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)) z τ) := by
  have h := summable_outer_decorationsG (memShape a mk y hy)
    (memberRBMk a mk y U hd1 hL1 base (hlay y hy) hB g cψ hc hg i)
    (source_disjMk a mk y hy) y.1.data hG P.γ P.δ (stateLayer y.1) tt amp frq Zw hZw hsum
  rw [memShape_lay_eq a mk y hy, memShape_hinges a mk y hy, memShape_route a mk y hy hG,
    memShape_hclk a mk y hy, memShape_hmom a mk y hy] at h
  simp only [member_ker_eqWMk a mk y hy _ _ _ _ _ _ (hcanM y hy) (hlay y hy)] at h
  exact h

end WaveTurbulence.Flower.MkUnits
