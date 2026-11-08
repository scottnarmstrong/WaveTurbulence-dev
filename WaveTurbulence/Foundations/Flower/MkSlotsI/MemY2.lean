/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.MemY1
public import WaveTurbulence.Foundations.Flower.MkSlots.IntMember2
public import WaveTurbulence.Foundations.Flower.MkSlotsT.MemberRun

/-! # B3s-HELPER7 MemY (part 1): the general member identity `member_skelValG`

For a member `y` of the run class of the representative `a` (unit marking `mk`, classes at `mkF`) and EVERY pattern
`pat`, depth selection `kSel`, stem scales `σ`, selection scales `Rs` and dagger datum `dag`: the frozen class summand
of `y.1.layered` (`kernelKgenSel` with the intrinsic pins `fixCap … pat`, the removed phases `offCap` and the marked
weight `markedWt`, at the selection `selPMk` of the fine′ class) is the `G_sb` dagger constant `capConstO` times the
weighted relaxed pinned skeleton value `skelValWZRL` of `y` with
* the units `blk_y = fun j => unitClBlock (y.2 j)`;
* the skeleton weight `[selSk ∧ Q] · Za`: `selSk` the common gap selection of `G_sb` at the restricted decoration
  (`selSkCMk ∘ resDec`, equal to α's `NormalizedSplice.selOf σy` by B3's `hZ_commonMk`), `Q = restIndO …` the dagger
  sibling indicator, `Za = genZa …` (`selOK · ∏_j [v_j] Rs_j⁻¹ · ∏_{non-hinge atoms} genNW`);
* the slot family `⟨slotFnGWFRL … anchProfiles … chainW … genΘs … (fixCap … pat), genTw …⟩`;
* the core pins `fixCore … (fixCap … pat)` and β's lower bounds `MkSlotsB.lbS … s`
(**`member_skelValG`**; α's `MkSlots.IntMember.member_skelVal` is the case `pat ≡ plain`, `σ ≡ kSel ≡ none`).
**`member_selAnd_ZwG`**: the indicator of `selSk ∧ Q` is α's `G_sb` weight `ZwG` at the restricted decoration.

Route: `classSummand_eq_genKernel` (MemW) → `selPMk_iff_related` (the selection of the fine′ class is the member's
`selAt`) → `genKernel_reconstruction` (MemY1) → `hZ_commonMk` (selection) → `prod_capNodeW_split` (dagger split) →
`member_reduction_gen` (MemRed) with `restW_cosetDecoration` (constant × indicator), β's pins (`relaxPins_fixCap`,
`lbSound_lbS`, `lbComplete_lbS`), WP4's factorization `genWeight_factor_Za` (MemY1; γ's `stemRet_member` when the weight
is stem-dependent) and the norm bounds; `member_restConst` turns the dagger constant into `capConstO`.

Hypotheses beyond α's `member_skelVal`: `hstem : ¬ StemDep σ kSel ∨ CleanPt J a` (γ's stem retention at the member
when stem-dependent), `hPatY : CapPatValid y.1.layered J pat p` and `hrootY` (every non-cap tree of the member carries
a capped flower; β's `MkSlotsB.exists_capFlower_of_capGeo` from irreducibility and `2·|J| = 2R`), used for β's
`RelaxPins` of the pattern pins. -/

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
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW restW capNodeW fixCore prod_capNodeW_split restW_none
  restW_cosetDecoration)
open WaveTurbulence.Flower.MkSlots.IntMember (restConstO restIndO capConstO ZwG)

namespace WaveTurbulence.Flower.MkSlotsI

/-- **The selection of the general member identity is α's `G_sb` weight**: the indicator of the common gap selection
at the restricted decoration and the dagger sibling indicator `restIndO` is `ZwG` at the restricted decoration. -/
theorem member_selAnd_ZwG (P : WTParams) (hL1 : 1 ≤ P.L) {R p : ℕ} {kind : Bool}
    (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (J : Finset (Fin (2 * R))) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hGeoY : CapGeo y.1.layered J p) (κ : GenDecoration y.1.skeleton P.d roots 0) :
    (if selAnd
        (fun κS => selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
        (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag) κ then (1 : ℝ)
      else 0) =
      ZwG a mk J P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' roots dag
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) := by
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  have hZ2 : MkSlots.sibIndAt J a (mk a.prime) dag (MkSlots.flwAt J a (mk a.prime))
      (cosetDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G P.L 0
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ).1) =
      if restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag κ then 1 else 0 := by
    cases dag with
    | none => simp [MkSlots.sibIndAt, restIndO]
    | some cc =>
      exact MkSlots.IntCore.member_sibInd a mk y hy hG J hcapA hcapY hrepU hGeoR P.L cc κ
  unfold ZwG
  rw [hZ2]
  unfold selAnd
  by_cases h1 : selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
      ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κ) <;>
    by_cases h2 : restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag κ <;>
    simp [h1, h2]

/-- **The general member identity.** A member's frozen class summand (every pattern, depth selection, stem scales,
selection scales and dagger datum) is the `G_sb` dagger constant times the member's weighted relaxed pinned skeleton
value with the atom weight `genZa`, the unit-top weight `genTw`, the slot kernels `slotFnGWFRL … chainW … genΘs …
(fixCap … pat)`, the core pins `fixCore … (fixCap … pat)` and β's lower bounds `lbS`. -/
theorem member_skelValG (P : WTParams) (hL1 : 1 ≤ P.L) (hd1 : 1 ≤ P.d) {R p : ℕ} {kind : Bool}
    {A : Finset (LayeredGarden (2 * R))} {mk mkF : Stage1Mk.MarkFn (2 * R)}
    (hFT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF)
    (π : PcA R p kind A mkF) (a : PrescribedPrimeGarden (2 * R)) (hπ : repPt π = a)
    (hout : a.outputs (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mkF)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (kSel σ : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (t s : ℝ) (hs : s ∈ Set.Ioo (p : ℝ) t) (ht : t ≤ p + 1)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hstem : ¬ StemDep σ kSel ∨ CleanPt J a)
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (hGeoY : CapGeo y.1.layered J p) (hPatY : CapPatValid y.1.layered J pat p)
    (hrootY : ∀ j ∉ J, ∃ ℓ : GLeaf y.1.layered.garden.tree, IsCapFlower y.1.layered J ℓ ∧ ℓ.1.1 = j) :
    kernelKgenSel P.L P.γ P.δ y.1.layered (fixCap y.1.layered J pat t s) (offCap y.1.layered J dag.isSome)
        (markedWt P J p kSel h Rf σ Rs dag y.1.layered) (fun _ => t) 0 roots
        (selPMk p kind A P 0 roots mkF π y.1.layered) =
      capConstO a mk J P.L P.γ P.δ s roots dag *
        skelValWZRL (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain P.L P.γ P.δ 0 roots (fun _ => t)
          (stateLayer y.1)
          (fun κ => if selAnd
              (fun κS => selSkCMk a mk P.L P.γ P.η (lt_of_lt_of_le zero_lt_one hL1).ne' 0 roots
                ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
              (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag) κ then
            genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
              (source_disjMk a mk y hy) J P.L σ kSel Rs 0 κ else 0)
          ⟨MkSlotsB.slotFnGWFRL y.1.data y.1.plain P.L P.γ P.δ
              (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
                h P.L roots)
              (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag)
              (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
              (stateLayer y.1) (stateLayer_isLayering y.1)
              (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
                pat t s),
            genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs⟩
          (fixCore y.1.data y.1.plain
            (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
              pat t s))
          (MkSlotsB.lbS y.1.data y.1.plain
            (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J
              pat t s) s) := by
  obtain ⟨M, hr, hn, hsh⟩ := memShape_data a mk y hy
  have hL0 : P.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  have hspec := stateLayer_spec y.1
  have hGeoR : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p := by
    rw [hspec]; exact hGeoY
  have hPatR : CapPatValid (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1))
      J pat p := by
    rw [hspec]; exact hPatY
  have hrootR : ∀ j ∉ J, ∃ ℓ : GLeaf (layeredReconstruction y.1.data y.1.plain (stateLayer y.1)
      (stateLayer_isLayering y.1)).garden.tree, IsCapFlower (layeredReconstruction y.1.data y.1.plain
        (stateLayer y.1) (stateLayer_isLayering y.1)) J ℓ ∧ ℓ.1.1 = j := by
    rw [hspec]; exact hrootY
  have hplain : y.1.layered.garden.IsPlain := by
    rw [← hspec]; exact y.1.data.garden_plain y.1.plain
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoR.cap_leaf
  -- the dagger constant and indicator
  have hrW : ∀ κ : GenDecoration (y.1.data.garden y.1.plain) P.d roots 0,
      restW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J dag
          (cosetDecoration (y.1.data.garden y.1.plain) P.L 0 κ.1) =
        if restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag
            (collapseGenDecoration y.1.data y.1.plain κ) then
          restConstO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J roots dag
        else 0 := by
    intro κ
    cases dag with
    | none =>
      refine (restW_none y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J _).trans ?_
      simp [restIndO, restConstO]
    | some cc =>
      exact restW_cosetDecoration y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hGeoR P.L P.γ
        P.δ s roots cc κ
  have hc : restConstO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J roots dag =
      capConstO a mk J P.L P.γ P.δ s roots dag := by
    cases dag with
    | none => rfl
    | some cc =>
      exact MkSlots.IntCore.member_restConst a mk y hy hG J hcapA hcapY hrepU hGeoR P.L P.γ P.δ s roots cc
  -- stem retention (only when the weight is stem-dependent)
  have hR : MkSlotsT.StemRet y.1.skeleton y.1.data.tree (fun j => unitClBlock (y.2 j))
      (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J ∨
      ((σ = fun _ => none) ∧ kSel = fun _ => none) := by
    rcases hstem with hn | hcl
    · right
      unfold StemDep at hn
      push Not at hn
      exact ⟨funext hn.1, funext hn.2⟩
    · exact Or.inl (MkSlotsT.stemRet_member a mk y hy J hcapA hcapY hcl)
  -- the selection of the fine′ class is the member's own selection
  have hrel : PrescribedPrimeGarden.Related (p := p) (kind := kind) (repPt π) (memberPointMk a mk y M hr) mkF :=
    hπ ▸ memberPoint_relatedMk hFT a hout y hy M hr
  have hprime : IsPrimeGarden y.1.skeleton := VineA.batch_prime hr.batch a.prime.prime
  set σy := transportGroupPrescription (batchMolIso hr.batch) a.sigma with hσy
  have hsel : selPMk p kind A P 0 roots mkF π y.1.layered = fun κ => selAt P 0
      ⟨y.1.skeleton, hprime, y.1.data, y.1.decodes⟩ σy κ :=
    funext fun κ => propext (selPMk_iff_related P 0 roots π (memberPointMk a mk y M hr) hrel y.1.layered rfl κ)
  have hiff : ∀ κS : GenDecoration y.1.skeleton P.d roots 0,
      NormalizedSplice.selOf σy P.L P.γ P.η 0 κS.1 ↔
        selSkCMk a mk P.L P.γ P.η hL0 0 roots ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS) := by
    intro κS
    have hZ1 : (if NormalizedSplice.selOf σy P.L P.γ P.η 0 κS.1 then (1 : ℝ) else 0) =
        if selSkCMk a mk P.L P.γ P.η hL0 0 roots
          ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS) then 1 else 0 := by
      rw [hsh]
      exact (hZ_commonMk a mk hr hn (markTransported_imageMark _ (mk a.prime)) (gapValueSelDartsMk_all (2 * R)) hL0
        P.γ P.η 0 roots κS).trans (selSkCMk_ite a mk P.L P.γ P.η hL0 0 roots _)
    by_cases h1 : NormalizedSplice.selOf σy P.L P.γ P.η 0 κS.1 <;>
      by_cases h2 : selSkCMk a mk P.L P.γ P.η hL0 0 roots
        ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS) <;>
      simp [h1, h2] at hZ1 ⊢
  -- the bounds
  obtain ⟨CΘ, hΘ⟩ := exists_norm_genZa_topW_le y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
    (memShape a mk y hy) (source_disjMk a mk y hy) J P.L σ kSel Rs (fun _ _ _ => 0) 0 roots 0
  obtain ⟨CΘs, hΘs⟩ := exists_norm_genΘs_le y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ
    kSel Rs (d := P.d)
  have hΘg := fun κ : GenDecoration (y.1.data.garden y.1.plain) P.d roots 0 =>
    genWeight_factor_Za y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
      (source_disjMk a mk y hy) J P.L σ kSel Rs hR (fun _ _ _ => 0) κ 0
  -- the chain
  refine (classSummand_eq_genKernel P J p pat kSel t s y.1.layered hGeoY hplain h Rf σ Rs dag roots
    (selPMk p kind A P 0 roots mkF π y.1.layered)).trans ?_
  rw [hsel]
  refine (genKernel_reconstruction P y.1.data y.1.plain hprime (stateLayer y.1) (stateLayer_isLayering y.1)
    y.1.layered hspec y.1.decodes σy J p pat kSel σ Rs t s h roots Rf dag).trans ?_
  refine (kernelLeavesSelNWFMR_congr_sel P.L P.γ P.δ
    (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) _ _ _ _ _ _
    (fun κ => selSkCMk a mk P.L P.γ P.η hL0 0 roots ((memShape a mk y hy).resDec y.1.plain
      (source_disjMk a mk y hy) (collapseGenDecoration y.1.data y.1.plain κ)))
    (fun κ => hiff (collapseGenDecoration y.1.data y.1.plain κ)) _ _ _).trans ?_
  refine (kernelLeavesSelNWFMR_congr_m P.L P.γ P.δ
    (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) _ _ _ _ _ _ _
    (fun k => (∏ z, chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag z
      (k z)) * restW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J dag k)
    (fun k => prod_capNodeW_split y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p
      s J Rf dag k) _ _).trans ?_
  refine (member_reduction_gen (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain P.L P.γ P.δ
    (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h P.L
      roots)
    (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s J Rf dag) 1 zero_le_one
    (MkSlots.IntMember.norm_chainW_le y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ p s
      J Rf dag)
    (stateLayer y.1) (stateLayer_isLayering y.1) (fun _ => t) 0 roots
    (fun ℓ _ => MkSlots.IntMember.anchProfiles_summable _ J p h P.L hL1 roots b hb hd1 hGeoR.layer_le hB ℓ 0)
    (fun κS => selSkCMk a mk P.L P.γ P.η hL0 0 roots
      ((memShape a mk y hy).resDec y.1.plain (source_disjMk a mk y hy) κS))
    (restIndO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L J dag)
    (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
    (MkSlotsB.lbS y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s)
    (relaxPins_fixCap hGeoR hPatR hrootR hs ht)
    (MkSlotsB.lbSound_lbS y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat t s)
    (MkSlotsB.lbComplete_lbS y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J pat t s)
    (restW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J dag)
    (restConstO y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) P.L P.γ P.δ s J roots dag) hrW
    (genTw y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs)
    (genZa y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (memShape a mk y hy)
      (source_disjMk a mk y hy) J P.L σ kSel Rs 0) CΘ hΘ
    (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J P.L σ kSel Rs) CΘs hΘs _ hΘg).trans ?_
  rw [hc]

end WaveTurbulence.Flower.MkSlotsI
