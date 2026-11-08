/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember1
public import WaveTurbulence.Foundations.Flower.MkUnits.WMember

/-! # B3s MK-SLOTS (integration, member identity 2): a member's class summand is a pinned skeleton value

For a member `y` of the run class of the representative `a` (at the marking `mk`, classes at `mkF`):
the frozen class summand of `y.1.layered` (`kernelKgenSel` with the plain intrinsic pins, the removed phases and the
marked weight, at the selection `selPMk` of the fine′ class) is the `G_sb` dagger constant `capConstO` times the
pinned skeleton value `skelValF` of `y` (pinned slot kernels with the chain node weight `chainW`, pins
`fixCore … fixCap`), at a skeleton selection `selSk` whose indicator is the `G_sb` weight `ZwG` (the piece's
dagger sibling indicator times the common gap selection `selSkCMk`) at the restricted decoration
(`member_skelVal`).

Route: `classSummand_eq_capKernel` (frozen summand = pinned weighted cap kernel) → `selPMk_iff_related` (the selection
of the fine′ class is the member's own `selAt`) → `capKernel_reconstruction` → `prod_capNodeW_split` +
`restW_cosetDecoration` + `kernelLeavesSelNWF_mul_ind` (the remaining dagger weight is a constant on the support of
`RestInd`) → `kernelLeaves_skeleton_reduction_selNWF`; `member_restConst`, `member_sibInd` (R-core) and B3's
`hZ_commonMk` for the selection. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.MkSlots.IntMember

open WaveTurbulence.Flower.MkSlots.IntRest WaveTurbulence.Flower.MkSlots.IntCore

section Defs
variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))

/-- The skeleton dagger support of a dagger datum (`True` without dagger). -/
def restIndO {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L : ℝ) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) {roots : Fin w → (Fin d → ℤ)} (κS : GenDecoration S d roots 0) : Prop :=
  dag.elim True fun cc => RestInd D hS layer hLayer L J cc κS

/-- The skeleton dagger constant of a dagger datum (`1` without dagger). -/
def restConstO {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (L γ δ s : ℝ) (J : Finset (Fin w))
    (roots : Fin w → (Fin d → ℤ)) (dag : Option (Fin w → Fin 3 → Mom d)) : ℂ :=
  dag.elim 1 fun cc => restConst D hS layer hLayer L γ δ s J roots cc

/-- **The `G_sb` dagger constant** of a dagger datum (`1` without dagger). -/
def capConstO {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) : ℂ :=
  dag.elim 1 fun cc => capConstG a mk J L γ δ s roots cc

theorem norm_capConstO {d : ℕ} (J : Finset (Fin (2 * R))) (L γ δ s : ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) : ‖capConstO a mk J L γ δ s roots dag‖ = 1 := by
  cases dag with
  | none => simp [capConstO]
  | some cc => exact norm_capConstG a mk J L γ δ s roots cc

/-- **The decoration weight of `G_sb`**: the piece's dagger sibling indicator times the common gap selection. -/
def ZwG {d : ℕ} (J : Finset (Fin (2 * R))) (L γ η : ℝ) (hL : L ≠ 0) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) : ℝ :=
  sibIndAt J a (mk a.prime) dag (flwAt J a (mk a.prime))
      (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0 z.1) *
    (if selSkCMk a mk L γ η hL 0 roots z then 1 else 0)

theorem sibIndAt_mem {d : ℕ} (J : Finset (Fin (2 * R))) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) (flw : GBranch (stM a Mk).G.tree → Fin 3 → Prop)
    (k : GNode (stM a Mk).G.tree → Mom d) :
    0 ≤ sibIndAt J a Mk dag flw k ∧ sibIndAt J a Mk dag flw k ≤ 1 := by
  unfold sibIndAt
  cases dag with
  | none => simp
  | some cc =>
    simp only [Option.elim]
    constructor
    · refine Finset.prod_nonneg fun c _ => ?_
      split_ifs
      · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
      · norm_num
    · refine Finset.prod_le_one₀ (fun c _ => ?_) fun c _ => ?_
      · split_ifs
        · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
        · norm_num
      · split_ifs
        · exact Finset.prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by split_ifs <;> norm_num
        · exact le_rfl

theorem ZwG_mem {d : ℕ} (J : Finset (Fin (2 * R))) (L γ η : ℝ) (hL : L ≠ 0) (roots : Fin (2 * R) → (Fin d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) :
    0 ≤ ZwG a mk J L γ η hL roots dag z ∧ ZwG a mk J L γ η hL roots dag z ≤ 1 := by
  have h := sibIndAt_mem a J (mk a.prime) dag (flwAt J a (mk a.prime))
    (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G L 0 z.1)
  unfold ZwG
  split_ifs
  · rw [mul_one]; exact h
  · rw [mul_zero]; exact ⟨le_rfl, zero_le_one⟩

end Defs

/-- **A member's class summand is the dagger constant times a pinned skeleton value.** -/
theorem member_skelVal (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ} {kind : Bool}
    {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
    (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (π : PcA R p kind A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
    (hout : a.outputs (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mkF)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (J : Finset (Fin (2 * R))) (t s : ℝ) (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hGeoY : CapGeo y.1.layered J p) :
    ∃ selSk : GenDecoration y.1.skeleton P.d roots 0 → Prop,
      (∀ κ, (if selSk κ then (1 : ℝ) else 0) = ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots dag
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ)) ∧
      kernelKgenSel P.L P.γ P.δ y.1.layered (fixCap y.1.layered J (fun _ => FixPat.plain) t s)
          (offCap y.1.layered J dag.isSome) (markedWt P J p (fun _ => none) h Rf (fun _ => none) Rs dag y.1.layered)
          (fun _ => t) 0 roots (selPMk p kind A P 0 roots mkF π y.1.layered) =
        capConstO a mk J P.L P.γ P.δ s roots dag *
          skelValF y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t) (stateLayer y.1) selSk
            (slotFnNWF y.1.data y.1.plain P.L P.γ P.δ
              (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
                h P.L roots)
              (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
              (stateLayer y.1) (stateLayer_isLayering y.1)
              (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                (fun _ => FixPat.plain) t s))
            (fixCore y.1.data y.1.plain
              (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                (fun _ => FixPat.plain) t s)) := by
  obtain ⟨M, hr, hn, hsh⟩ := memShape_data a mk y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hplain : y.1.layered.garden.IsPlain := by
    rw [← hspec]; exact y.1.data.garden_plain y.1.plain
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hcap' : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hcapA
  -- the frozen summand is the pinned weighted cap kernel
  have e1 := classSummand_eq_capKernel P J p t s y.1.layered hGeoY hplain hs ht h Rf Rs dag roots
    (selPMk p kind A P 0 roots mkF π y.1.layered)
  -- the selection of the fine′ class is the member's own selection
  have hrel : PrescribedPrimeGarden.Related (p := p) (kind := kind) (repPt π) (memberPointMk a mk y M hr) mkF :=
    hπ ▸ memberPoint_relatedMk hFT a hout y hy M hr
  have hprime : IsPrimeGarden y.1.skeleton := VineA.batch_prime hr.batch a.prime.prime
  set σy := transportGroupPrescription (batchMolIso hr.batch) a.sigma with hσy
  have hsel : selPMk p kind A P 0 roots mkF π y.1.layered = fun κ => selAt P 0
      ⟨y.1.skeleton, hprime, y.1.data, y.1.decodes⟩ σy κ :=
    funext fun κ => propext (selPMk_iff_related P 0 roots π (memberPointMk a mk y M hr) hrel y.1.layered rfl κ)
  have e2 := congrArg (fun sel => kernelLeavesSelNWF P.L P.γ P.δ y.1.layered (anchProfiles J y.1.layered h P.L roots)
    (fun _ => t) 0 0 roots 0 sel (fun k => ∏ z, capNodeW P.L P.γ P.δ p s y.1.layered J Rf dag z (k z))
    (fixCap y.1.layered J (fun _ => FixPat.plain) t s)) hsel
  have e3 := capKernel_reconstruction P y.1.data y.1.plain hprime (stateLayer y.1) (stateLayer_isLayering y.1)
    y.1.layered hspec y.1.decodes σy J p t s h roots Rf dag
  -- split the node weight; the remaining dagger weight is a constant on its support
  have hsplit : (fun k => ∏ z, capNodeW P.L P.γ P.δ p s
        (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J Rf dag z (k z)) =
      fun k => (∏ z, chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag z
        (k z)) * restW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J dag k :=
    funext fun k => prod_capNodeW_split y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p
      s J Rf dag k
  have e4 := congrArg (fun m => kernelLeavesSelNWF P.L P.γ P.δ
    (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
    (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
      roots) (fun _ => t) 0 0 roots 0
    (fun κ => NormalizedSplice.selOf σy P.L P.γ P.η 0 (collapseGenDecoration y.1.data y.1.plain κ).1) m
    (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (fun _ => FixPat.plain) t s)) hsplit
  have e5 := kernelLeavesSelNWF_mul_ind P.L P.γ P.δ
    (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
    (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
      roots) (fun _ => t) 0 0 roots 0
    (fun κ => NormalizedSplice.selOf σy P.L P.γ P.η 0 (collapseGenDecoration y.1.data y.1.plain κ).1)
    (fun κ => restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag
      (collapseGenDecoration y.1.data y.1.plain κ))
    (fun k => ∏ z, chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag z
      (k z))
    (restW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J dag)
    (restConstO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J roots dag)
    (fun κ => by
      cases dag with
      | none =>
        refine (restW_none y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J _).trans ?_
        exact (if_pos (show restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J
          (none : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (collapseGenDecoration y.1.data y.1.plain κ) from
            trivial)).symm
      | some cc =>
        exact restW_cosetDecoration y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hGeoR P.L P.γ
          P.δ s roots cc κ)
    (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (fun _ => FixPat.plain) t s)
  -- the pinned skeleton reduction
  set selSk : GenDecoration y.1.skeleton P.d roots 0 → Prop := fun κS =>
    NormalizedSplice.selOf σy P.L P.γ P.η 0 κS.1 ∧
      restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag κS with hselSk
  have hred := kernelLeaves_skeleton_reduction_selNWF y.1.data y.1.plain P.L P.γ P.δ
    (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
      roots)
    (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag) 1 zero_le_one
    (norm_chainW_le y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
    (stateLayer y.1) (stateLayer_isLayering y.1) (fun _ => t) 0 roots 0
    (fun ℓ _ => anchProfiles_summable _ J p h P.L hL1 roots b hb hd1 hGeoR.layer_le hB ℓ 0) selSk
    (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
      (fun _ => FixPat.plain) t s)
  refine ⟨selSk, fun κ => ?_, ?_⟩
  · -- the selection indicator
    have hZ1 : (if NormalizedSplice.selOf σy P.L P.γ P.η 0 κ.1 then (1 : ℝ) else 0) =
        if selSkCMk a mk P.L P.γ P.η hL0 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) then 1 else 0 := by
      rw [hsh]
      exact (hZ_commonMk a mk hr hn (markTransported_imageMark _ (mk a.prime)) (gapValueSelDartsMk_all (2 * R)) hL0
        P.γ P.η 0 roots κ).trans (selSkCMk_ite a mk P.L P.γ P.η hL0 0 roots _)
    have hZ2 : sibIndAt J a (mk a.prime) dag (flwAt J a (mk a.prime))
        (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L 0
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ).1) =
        if restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag κ then 1 else 0 := by
      cases dag with
      | none => simp [sibIndAt, restIndO]
      | some cc =>
        exact member_sibInd a mk y hy hG J hcap' hcapY hrepU hGeoR P.L cc κ
    unfold ZwG
    rw [hZ2, ← hZ1]
    simp only [hselSk]
    by_cases h1 : NormalizedSplice.selOf σy P.L P.γ P.η 0 κ.1 <;>
      by_cases h2 : restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag κ <;>
      simp [h1, h2]
  · have hc : restConstO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J roots dag =
        capConstO a mk J P.L P.γ P.δ s roots dag := by
      cases dag with
      | none => rfl
      | some cc =>
        exact member_restConst a mk y hy hG J hcap' hcapY hrepU hGeoR P.L P.γ P.δ s roots cc
    rw [← hc]
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (congrArg _ hred)))))

end WaveTurbulence.Flower.MkSlots.IntMember
