/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm3

/-! # B3s MK-SLOTS (integration, assembly 4): **`classRepAlphaJ_at`**

`ClassRepAlphaJ cP` at the record `withC₁ (PB Pg C) (c_F^{16})` for `37 ≤ cP`, from B3's gates at `Pg`, V5W's
weighted class bound and the top decay at `PB Pg C`, the cap-slot obligation `CapSlotObligationAt Kc (PB Pg C)` and
`C ≥ CalphaJ Pg.d Pg.η Pg.C₁ Kc`. Adapted from `MkUnits/WAssembly.lean` (`vineCaseRepresentsFWMk_of_gate`, see
`COPIED-SHA256SUMS`): the engine is the pinned `representsIntMK_of_vineModesFix` at the α piece at the unit marking
`mkU a.prime = classMk mkF a`, the family is `capFam`, the class sum `class_modes`, the sign the dagger constant
`capConstO` (one type index). The vine-free case (`unitBlocks = []`) is included: nothing uses a unit.

Mass: `(∏ slot leaf factors) · (∏ unit factors) ≤ c_F^{16N} b^{N+R}` (B3) and one factor `b⁻¹ L^{31d+6}` per cap
slot, `|J| = R` cap slots (`prod_capSlot`), so the engine mass is `c_F^{16N} · L^{(31d+6)R} · b^N`; then
`pieceAt_C₁_lift` (`c_F^{16N} = (c_F^{16})^N` into `C₁`) and `pieceAt_absorb` (`(31d+6)R ≤ cP·d·nProt`,
`R ≤ nProt = |Π|`, `37 ≤ cP`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlots.IntAsm
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
  WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots.IntMember WaveTurbulence.Flower.MkSlots.IntCore
open scoped ENNReal Classical

/-- **`ClassRepAlphaJ` at one parameter record.** -/
theorem classRepAlphaJ_at (Pg : WTParams) (C : ℝ) (E : GateEnv Pg) (htop0 : TopIncoherentDecayAtR Pg)
    (hη : 0 < Pg.η) (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM)
    (Kc : ℕ → ℝ → ℝ) (hC : CalphaJ Pg.d Pg.η Pg.C₁ Kc ≤ C)
    (hV : V5FrontierClassBoundAt (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C))
    (hcap : CapSlotObligationAt Kc (PB Pg C)) (cP : ℝ) (hcP : 37 ≤ cP) :
    ClassRepAlphaJ cP (withC₁ (PB Pg C) (frontierConst Pg.d ^ 16)) := by
  intro p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs hpat hk A hA hpl hTC roots hh b Rf σ Rs dag hσ hb hsn hRf
    hRs hhigh mkF hmk π hπ
  have hpat' : pat = fun _ => FixPat.plain := funext hpat
  have hk' : kSel = fun _ => none := funext hk
  have hσ' : σ = fun _ => none := funext hσ
  subst hpat' hk' hσ'
  -- constants (as in B3's `vineCaseRepresentsFWMk_of_gate`)
  have hCv : CvineFW Pg.d Pg.η Pg.C₁ ≤ C := le_trans (le_max_left _ _) hC
  obtain ⟨K, hK1, hKe, hslot⟩ := vine_slot_dataWMk Pg E htop0
  have hC1' : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCv
  have hC1ge : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCv
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * max K (Kc Pg.d Pg.η)) ^ 2 * ChFW Pg.d Pg.η ≤ C := by
    rw [hKe]; exact le_trans (le_max_right _ _) hC
  have hcLeib := cLeib_nonneg Pg.d (30 * Pg.d)
  obtain ⟨hη6, hη1, hη12⟩ := eta_small_facts Pg.η hη E.hη
  have hCg : Pg.C₁ ≤ C := by nlinarith [E.hC1]
  have hgate : CoherentGateH (PB Pg C) :=
    coherentGateH_of (leafwiseCoherentApproximation30_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl
      E.hcoh)
  have hinc : IncoherentGateH (PB Pg C) :=
    incoherentGateH_of (leafwiseIncoherentDecay_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hinc)
  have hd1 : 1 ≤ Pg.d := E.hd1
  have hL1 : 1 ≤ Pg.L := E.hL1
  have hL0 : 0 < Pg.L := lt_of_lt_of_le zero_lt_one hL1
  have hcψ : 1 ≤ frontierConst Pg.d := one_le_frontierConst _
  have hc0 : 0 ≤ frontierConst Pg.d := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hNe : (withC₁ (PB Pg C) (frontierConst Pg.d ^ 16)).N (p + 1) = Pg.N (p + 1) :=
    (N_bumpC1 (PB Pg C) _ (p + 1)).trans (N_bumpC1 Pg C (p + 1))
  have hN2' : N ≤ Pg.N (p + 1) ^ 4 := by rw [← hNe]; exact hN2
  have hp' : p < Pg.D := hp
  -- the representative
  have haA : (repPt π).layered ∈ A := repPt_layered_memMk π
  have hcA := hA (repPt π).layered haA
  have hcan : IsCanonGC (p + 1) (repPt π).layered := hcA.1.1
  have hordN : (repPt π).layered.garden.order = N := hcA.1.2.2.1
  have hirr : (repPt π).layered.garden.Irreducible := hcA.2.2.1
  have hGeo : CapGeo (repPt π).layered J p := hcA.2.2.2.2.1
  have hdec := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
  have hsz : (repPt π).prime.data.size ≤ Pg.N (p + 1) ^ 4 := by omega
  have hMa := Mole.garden_isMolecule (repPt π).prime.skeleton
  -- the markings: units at `mkU (repPt π).prime = classMk mkF (repPt π)`, classes at `mkF`
  obtain ⟨T, hT⟩ := exists_outputs_finsetMk (p := p) (repPt π) mkF
  obtain ⟨mkU, hset, hout⟩ : ∃ mkU : Stage1Mk.MarkFn (2 * R), mkU (repPt π).prime = mkAt mkF (repPt π) ∧
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
        (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF :=
    ⟨fixMark (repPt π) (mkAt mkF (repPt π)), fixMark_self (repPt π) (mkAt mkF (repPt π)),
      outputs_fixMark_mkAt mkF (repPt π)⟩
  have hadm : AdmP R J (fun _ => FixPat.plain) t s (fun _ => none) (sourceStart (repPt π) mkU) := by
    show AdmP R J _ t s _ (startAt (repPt π) (mkU (repPt π).prime))
    rw [hset]
    exact startAt_admP J _ t s _ (repPt π) mkF hmk.sub
  have hcl := twistClosedAdm_of_marked hTC
  have hmem : ∀ y : UState (2 * R) (unitsSplit (sourceAssemblyMk (repPt π) mkU)),
      y ∈ sourceClass (repPt π) p (objKind (2 * R)) mkU → CapGeo y.1.layered J p ∧ IsCanonGC (p + 1) y.1.layered :=
    fun y hy => ⟨(hA _ (outputs_mem_AMk hcl (repPt π) mkU hadm haA hcan y hy)).2.2.2.2.1,
      (hA _ (outputs_mem_AMk hcl (repPt π) mkU hadm haA hcan y hy)).1.1⟩
  have hGplain : (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G.IsPlain :=
    (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1
  have hGeoA : CapGeo (layeredReconstruction (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
      (sourceLayer_isLayering (repPt π))) J p := by
    rw [sourceLayer_reconstructs (repPt π)]; exact hGeo
  have hrepU := fun j b hb => rep_units_not_cfp J t s mkF hmk.sub (repPt π) mkU hset j b hb
  -- B3's slot data at the unit marking, the cap pieces
  have hctrl_a : ∀ i, LeafwiseControlled (repPt π).layered
      (typeProfiles (repPt π).layered ((uFam (PB Pg C) hh b).h i)) (fun _ => (uFam (PB Pg C) hh b).b i) :=
    fun _ => leafwise_of_bound (repPt π).layered p hGeo.layer_le hh b hb0 hsn
  have hgp : ∀ j, GPresented (32 * Pg.d) (frontierG (Rf j)) (frontierConst Pg.d) := fun j =>
    gPresented_frontierG Pg.d (Rf j) (fun r hr => by have := hRf j r hr; show (1 : ℝ) ≤ r; linarith)
  have htt : ∀ j, (fun _ => t : Fin (2 * R) → ℝ) j ∈ Set.Icc (p : ℝ) (p + 1) := fun _ => ⟨ht.1.le, ht.2.le⟩
  obtain ⟨fam, μ, hexpR, hμ, hμb⟩ := hslot C hC1' (repPt π) mkU hp' hcan hsz (fun _ => t) htt (uFam (PB Pg C) hh b)
    hctrl_a (fun j => frontierG (Rf j)) (frontierConst Pg.d) hcψ hgp hGplain
  have hszC : (repPt π).prime.data.size ≤ (PB Pg C).N (p + 1) ^ 4 := by rw [N_bumpC1]; exact hsz
  obtain ⟨pc, hpcv, hpcm⟩ := exists_capPieces (PB Pg C) Kc hcap C le_rfl (repPt π) mkU hGplain J t s hp' hcan hszC
    hGeo hirr ht hs roots hh b hb hsn Rf hRf dag
  -- cap trees and cap pairs of `G_sb`
  have hcapG : ∀ j ∈ J, (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G.tree j =
      TTree.leaf := fun j hj =>
    shape_tree_leaf (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (skel_tree_leaf (repPt π).prime.data (repPt π).prime.prime.1 (hGeoA.cap_leaf j hj))
  have hGirr : (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G.Irreducible :=
    (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).irred (repPt π).prime.prime.1
      (skeleton_irreducible (repPt π).prime hirr)
  have hccG := no_capcap_of_irred _ hGplain hGirr J hJ hcapG
  -- the protected loss `L^{(31d+6)R}` fits in `L^{cP d nProt}`
  have hnP : R ≤ (protI (repPt π).layered J (fun _ => FixPat.plain) t s (fun _ => none)).card :=
    card_le_protI _ J hJ _ t s _
  have hℓ : (31 * (Pg.d : ℝ) + 6) * R ≤
      cP * Pg.d * ((protI (repPt π).layered J (fun _ => FixPat.plain) t s (fun _ => none)).card : ℝ) :=
    loss_le Pg.d R _ cP hcP hd1 hnP
  refine pieceAt_absorb (withC₁ (PB Pg C) (frontierConst Pg.d ^ 16)) J t s _ (repPt π) _ dag hL1 hℓ ?_
  refine representsIntMK_pieceAt_congr (withC₁ (PB Pg C) (frontierConst Pg.d ^ 16)) J t s _ (repPt π) dag hset ?_
  rw [classValue_withC₁]
  refine pieceAt_C₁_lift (PB Pg C) (frontierConst Pg.d ^ 16) (one_le_pow₀ hcψ) J t s _ (repPt π)
    (mkU (repPt π).prime) dag ?_
  -- the class value as a mode sum
  rw [classValue_eq_outputs (PB Pg C) J _ _ t s A hTC roots hh Rf _ Rs dag mkF hmk π hcan T hT,
    class_modes (PB Pg C) hL1 hd1 hmk.fine π (repPt π) rfl hout hGplain J t s hs ht.2.le hh b hb0 hsn roots Rf Rs dag
      hGeoA.cap_leaf hrepU hGeoA (fam ()) (hexpR ()) pc hpcv hmem T hT]
  -- unit masses (B3)
  have hmc : ∀ j, unitMassC (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
      (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (frontierConst Pg.d)
      b.toNNReal =
      frontierConst Pg.d ^ (9 * (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).atoms.card +
        4 * clLocalOrder2 (repPt π).prime.data (repPt π).prime.prime.1
          (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))) *
      unitMass (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data (repPt π).prime.prime.1
        (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) b.toNNReal := fun j => rfl
  have hM0 : ∀ j, 0 ≤ unitMass (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
      (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) b.toNNReal := fun j => by
    unfold unitMass
    have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
      mul_nonneg (by show (0 : ℝ) ≤ C; linarith) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by show (0 : ℝ) ≤ Pg.L; linarith) _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
  have hMC0 : ∀ j, 0 ≤ unitMassC (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
      (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (frontierConst Pg.d)
      b.toNNReal := fun j => by
    rw [hmc]; exact mul_nonneg (pow_nonneg hc0 _) (hM0 j)
  have hn : N - (repPt π).prime.skeleton.order = (repPt π).prime.data.size := by omega
  have hnS : (repPt π).prime.skeleton.order ≤ N := by omega
  have hordD : ((repPt π).prime.data.garden (repPt π).prime.prime.1).order = N := by
    rw [(repPt π).prime.gardenEq, hordN]
  have hplainA : (repPt π).layered.garden.IsPlain := by
    rw [← sourceLayer_reconstructs (repPt π)]; exact (repPt π).prime.data.garden_plain _
  have hSL0 : ∀ sl, 0 ≤ slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
      (sourceLayer_isLayering (repPt π)) (fun _ => b.toNNReal)
      ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) := by
    intro sl
    generalize (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl = s0
    unfold slotLeaf
    rcases s0 with p' | b'
    · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hLe0 : 0 ≤ Pg.L ^ (31 * (Pg.d : ℝ) + 6) := Real.rpow_nonneg hL0.le _
  -- the engine
  have hGsb := hGplain
  refine representsIntMK_of_vineModesFix (P := PB Pg C) hd1 hL1 E.hη0
    (pieceAt (PB Pg C) J t s (fun _ => none) (repPt π) (mkU (repPt π).prime) dag) hGplain (fun _ => t) 0 roots
    (selSkCMk (repPt π) mkU (PB Pg C).L (PB Pg C).γ (PB Pg C).η hL0.ne' 0 roots) ?hgsp ?hslice
    (fun c _ h' => by rw [pieceAt_filt] at h'; exact absurd h' (by simp))
    (fun k => sibIndAt_mem (repPt π) J (mkU (repPt π).prime) dag (flwAt J (repPt π) (mkU (repPt π).prime)) k)
    0 le_rfl
    ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).route (repPt π).prime.prime.1 hGplain)
    (fun sl i => (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).route_natural (repPt π).prime.prime.1
      hGplain sl i)
    ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).hclk
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)))
    ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).hmom
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)))
    (stSrc hMa (repPt π).totalSigma hGplain)
    (fun j i x hx z => stSrc_dartMk hMa (repPt π).totalSigma hGplain j i x hx roots z)
    (fun j i r hr z => stSrc_rootMk hMa (repPt π).totalSigma hGplain j i r hr roots z)
    (fun _ : Unit => capConstO (repPt π) mkU J Pg.L Pg.γ Pg.δ s roots dag)
    (fun _ => le_of_eq (norm_capConstO (repPt π) mkU J Pg.L Pg.γ Pg.δ s roots dag))
    (fun _ => capFam hGplain J (fam ()) pc)
    (fun _ sl => if IsCapSlot hGplain J sl then
      ENNReal.ofReal (Kc Pg.d Pg.η * (C * Real.sqrt Pg.δ) ^ slotSize (repPt π).prime.data
          ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
        Pg.L ^ (-(Pg.η ^ 8) * (slotIncoh (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
          (sourceLayer_isLayering (repPt π))
          ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) : ℝ)) *
        (frontierConst Pg.d ^ Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
            ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
          (b⁻¹ * slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
            (sourceLayer_isLayering (repPt π)) (fun _ => b.toNNReal)
            ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl))) *
        Pg.L ^ (31 * (Pg.d : ℝ) + 6))
      else μ () sl)
    (fun _ j lam t' k => unitHkFW (PB Pg C) p (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
      (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (fun j => frontierG (Rf j))
      (unitProfile (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime)) hh j) 0 lam t' k)
    (c := 6 * (PB Pg C).η ^ 6) (θ := (PB Pg C).η) (by positivity) hη1 hη12 ?hμ
    ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) (max K (Kc Pg.d Pg.η)) (ChFW Pg.d Pg.η) rfl
    (le_trans hK1 (le_max_left _ _)) (le_max_left _ _) hCχ
    (fun sl => slotSize (repPt π).prime.data
      ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl))
    (fun sl => slotIncoh (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
      (sourceLayer_isLayering (repPt π))
      ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl))
    (fun _ sl => frontierConst Pg.d ^ Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
      slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
        (fun _ => b.toNNReal)
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
      (if IsCapSlot hGplain J sl then b⁻¹ * Pg.L ^ (31 * (Pg.d : ℝ) + 6) else 1))
    ?hlf ?hμb
    (fun _ j => unitMassC (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
      (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (frontierConst Pg.d)
      b.toNNReal)
    (fun j => clLocalOrder2 (repPt π).prime.data (repPt π).prime.prime.1
      (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j)))
    (fun j => cohmolIndex (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data (repPt π).prime.prime.1
        (sourceLayer (repPt π)) +
      (step3D hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data (repPt π).prime.prime.1
        (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
        (canonBadKind hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data (repPt π).prime.prime.1
          (sourceLayer (repPt π)))
        (qOutOf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
          (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).upper
          (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).lower
          (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j)))
        (fun _ => (0 : Mom (PB Pg C).d)) (0 : Mom (PB Pg C).d)).M₁)
    (fun j => (Finset.univ.filter fun i : Fin (unitN (repPt π).totalSigma j) =>
      (assemblyShape hM9 (sourceAssemblyMk (repPt π) mkU j)).nor i = false).card)
    (fun _ j => frontierConst Pg.d ^ (9 * (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).atoms.card +
        4 * clLocalOrder2 (repPt π).prime.data (repPt π).prime.prime.1
          (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))) *
      regionLeafSize (repPt π).prime.data (repPt π).prime.prime.1
        (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))
        (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (fun _ => ((b.toNNReal : NNReal) : ℝ)))
    ?hlfj ?hM ?hhinge N _ ?hs ?hexp ?hg ?hb ?hh ?hJ _ ?hval
  case hgsp =>
    intro D' hD z
    exact normalizedPiece_gapIndicatorMk (repPt π) mkU D' hD hL0.ne' _ _ 0 roots z
  case hslice =>
    intro τ
    exact mem_splicedTimeDomain_slice_lb _ _ _ _
      (admissibleAt J p mkF (repPt π) hGeo t s hs ht.2 (mkU (repPt π).prime) hset) τ
  case hμ =>
    intro i sl
    have hm := mass_combineFam (fam ()) (IsCapSlot hGplain J) (capPieces pc) sl (PB Pg C).η
    refine (le_of_eq hm).trans ?_
    by_cases hc : IsCapSlot hGplain J sl
    · rw [if_pos hc, if_pos hc]
      obtain ⟨q, rfl, hq⟩ := hc
      exact hpcm q hq
    · rw [if_neg hc, if_neg hc]
      exact hμ () sl
  case hlf =>
    intro i sl
    refine mul_nonneg (mul_nonneg (pow_nonneg hc0 _) (hSL0 sl)) ?_
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr hb0) hLe0
    · exact zero_le_one
  case hμb =>
    intro i sl
    have hX : 0 ≤ ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) ^ slotSize (repPt π).prime.data
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) :=
      pow_nonneg (mul_nonneg (by show (0 : ℝ) ≤ C; linarith) (Real.sqrt_nonneg _)) _
    have hY : 0 ≤ (PB Pg C).L ^ (-((PB Pg C).η ^ 8) * (slotIncoh (repPt π).prime.data (repPt π).prime.prime.1
        (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) : ℝ)) :=
      Real.rpow_nonneg hL0.le _
    have hZ : 0 ≤ frontierConst Pg.d ^ Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
      slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
        (fun _ => b.toNNReal)
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) :=
      mul_nonneg (pow_nonneg hc0 _) (hSL0 sl)
    by_cases hc : IsCapSlot hGplain J sl
    · simp only [if_pos hc]
      refine ENNReal.ofReal_le_ofReal ?_
      have hK : Kc Pg.d Pg.η ≤ max K (Kc Pg.d Pg.η) := le_max_right _ _
      have hW : 0 ≤ b⁻¹ * Pg.L ^ (31 * (Pg.d : ℝ) + 6) := mul_nonneg (inv_nonneg.mpr hb0) hLe0
      have hall := mul_le_mul_of_nonneg_right hK (mul_nonneg (mul_nonneg (mul_nonneg hX hY) hZ) hW)
      calc _ = Kc Pg.d Pg.η * (((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) ^ slotSize (repPt π).prime.data
              ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
            (PB Pg C).L ^ (-((PB Pg C).η ^ 8) * (slotIncoh (repPt π).prime.data (repPt π).prime.prime.1
              (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
              ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) :
                ℝ)) *
            (frontierConst Pg.d ^ Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
                ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl) *
              slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
                (sourceLayer_isLayering (repPt π)) (fun _ => b.toNNReal)
                ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain sl)) *
            (b⁻¹ * Pg.L ^ (31 * (Pg.d : ℝ) + 6))) := by
            show _ = Kc Pg.d Pg.η * ((C * Real.sqrt Pg.δ) ^ _ * Pg.L ^ _ * _ * _)
            ring
        _ ≤ _ := hall
        _ = _ := by show _ = max K (Kc Pg.d Pg.η) * (C * Real.sqrt Pg.δ) ^ _ * Pg.L ^ _ * (_ * _ * _); ring
    · simp only [if_neg hc, mul_one]
      refine (hμb () sl).trans (ENNReal.ofReal_le_ofReal ?_)
      have hK : K ≤ max K (Kc Pg.d Pg.η) := le_max_left _ _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hX) hY) hZ
  case hlfj =>
    intro i j
    exact mul_nonneg (pow_nonneg hc0 _)
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
  case hM =>
    intro i j
    refine ⟨hMC0 j, le_of_eq ?_⟩
    rw [hmc]
    unfold unitMass
    rw [nor_card_eq hM9 (sourceAssemblyMk (repPt π) mkU j)]
    simp only [neg_mul]
    ring
  case hhinge =>
    intro i ξ
    have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
    have hordg : ((repPt π).prime.data.garden (repPt π).prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
      rw [hordD, N_bumpC1]; exact hN2'
    obtain ⟨H, Mh, hsum', hHk, hprod⟩ := unit_hinge_dataWMk (PB Pg C) hV hM9 hgate hinc htop hd1 hη hη6 E.hη hC1ge
      hδ hL1 hw hp' (repPt π) mkU hcan hordg (fun _ => t) 0 roots (fun j => frontierG (Rf j)) (frontierConst Pg.d)
      hcψ hgp (fun j x => frontierG_im _ x) hh b hb0 (fun q j j' hq => hsn q hq j j')
      (modLam (fun sl => (capFam hGplain J (fam ()) pc).m sl (ξ sl))
        ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).route (repPt π).prime.prime.1 hGplain))
    refine ⟨H, Mh, hsum', ?_, ?_⟩
    · exact hHk
    · have hpt : ∀ j, ChinFW (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j)
          (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
          (frontierConst Pg.d) b ≤
          ChFW Pg.d Pg.η * unitMassC (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
            (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (frontierConst Pg.d)
            b.toNNReal := fun j => by
        have e : ChinFW (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j)
            (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
            (frontierConst Pg.d) b =
            (ChinFW Pg.d Pg.η * topFilterMass) * unitMassC (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j)
              (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π))
              (frontierConst Pg.d) b.toNNReal := by
          unfold unitMassFW unitMassC
          rw [Real.coe_toNNReal b hb0]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hMC0 j)
      have hlam : 0 ≤ ∏ j, (1 + |((modLam (fun sl => (capFam hGplain J (fam ()) pc).m sl (ξ sl))
          ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).route (repPt π).prime.prime.1 hGplain) j : ℤ) :
            ℝ)|) ^ (6 * (PB Pg C).η ^ 6) :=
        Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
      have hch := ChinFW_spec Pg.d Pg.η E.hη0
      rw [hprod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun j _ => mul_nonneg hch
        (unitMassFW_nonneg (PB Pg C) hM9 (sourceAssemblyMk (repPt π) mkU j) (repPt π).prime.data
          (repPt π).prime.prime.1 (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (frontierConst Pg.d) b
          hc0 (by show (0 : ℝ) ≤ C; linarith) hL0 hb0))
        (fun j _ => hpt j)) hlam
  case hexp =>
    exact exponent_order (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
      hGplain N hn hnS
  case hg =>
    have h1 := gsk_boundMk (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
      hGplain (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (repPt π).totalSigma
      (B₀ := sourceAssemblyMk (repPt π) mkU) (Mk := mkU (repPt π).prime) (hcov_unitsMk hMa (repPt π).totalSigma)
      (fun v => sourceLayer (repPt π) ((repPt π).prime.data.coreBranch (repPt π).prime.prime.1 v).toNode)
      (fun v => rfl)
    have h2 := gsk_of_specMk (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
      (sourceLayer_isLayering (repPt π)) (repPt π).layered (sourceLayer_reconstructs (repPt π))
      (repPt π).prime.decodes (repPt π).totalSigma (Mk := mkU (repPt π).prime)
    refine le_trans (le_of_eq h2) (le_trans h1 (le_of_eq ?_))
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [step3D_M1]
    rfl
  case hb =>
    exact bsk_boundMk hM9 (repPt π).totalSigma (sourceAssemblyMk (repPt π) mkU) (Mk := mkU (repPt π).prime)
      (hcov_unitsMk hMa (repPt π).totalSigma)
  case hh =>
    exact le_of_eq ((card_hinges (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime))).symm.trans
      (congrArg Finset.card (stShape_hingesMk hMa (repPt π).totalSigma (mkU (repPt π).prime))))
  case hJ =>
    exact card_units_le_order (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime))
  case hval =>
    rw [Fintype.sum_unique]
    have hZ : (fun z => ((ZwG (repPt π) mkU J (PB Pg C).L (PB Pg C).γ (PB Pg C).η hL0.ne' roots dag z : ℝ) : ℂ)) =
        fun z => pieceAtomW (pieceAt (PB Pg C) J t s (fun _ => none) (repPt π) (mkU (repPt π).prime) dag)
          (cosetDecoration (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G
            (PB Pg C).L 0 z.1) *
          (if selSkCMk (repPt π) mkU (PB Pg C).L (PB Pg C).γ (PB Pg C).η hL0.ne' 0 roots z then 1 else 0) :=
      funext fun z => (pieceAtomW_pieceAt (PB Pg C) J t s (repPt π) mkU dag hL0.ne' roots z).symm
    rw [hZ]
    rfl
  case hs =>
    rw [Fintype.sum_unique, norm_capConstO, one_mul, Finset.prod_mul_distrib]
    erw [prod_capSlot _ hGplain J hcapG hccG]
    rw [hJ]
    have hexpo := weight_exponent_le (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
      (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
      hGplain N hn hnS
    have hE : (∑ s', Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
          ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain s')) +
        ∑ j, (9 * (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).atoms.card +
          4 * clLocalOrder2 (repPt π).prime.data (repPt π).prime.prime.1
            (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))) ≤ 16 * N := by
      rw [hordD] at hexpo; omega
    have hprodeq : (∏ t, slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
          (sourceLayer_isLayering (repPt π)) (fun _ => b.toNNReal)
          ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain t)) *
        ∏ j, regionLeafSize (repPt π).prime.data (repPt π).prime.prime.1
          (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))
          (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (fun _ => ((b.toNNReal : NNReal) : ℝ)) =
        b ^ (N + R) := by
      rw [leaf_prod_split (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
        (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
        hGplain (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) b.toNNReal, sourceLayer_reconstructs]
      exact leafSizeProduct_const (repPt π).layered hplainA hordN b hb0
    have hfac : (∏ t, (frontierConst Pg.d ^ Stage1WNoVine.slotNr (repPt π).prime.data (repPt π).prime.prime.1
            ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain t) *
          slotLeaf (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
            (sourceLayer_isLayering (repPt π)) (fun _ => b.toNNReal)
            ((stShape hMa (repPt π).totalSigma (mkU (repPt π).prime)).iota (repPt π).prime.prime.1 hGplain t))) *
        ∏ j, (frontierConst Pg.d ^ (9 * (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j).atoms.card +
          4 * clLocalOrder2 (repPt π).prime.data (repPt π).prime.prime.1
            (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))) *
          regionLeafSize (repPt π).prime.data (repPt π).prime.prime.1
            (regionOf (unitBlkMk hMa (repPt π).totalSigma (mkU (repPt π).prime) j))
            (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (fun _ => ((b.toNNReal : NNReal) : ℝ))) ≤
        frontierConst Pg.d ^ (16 * N) * b ^ (N + R) := by
      rw [prod_pow_mul_prod, prod_pow_mul_prod, mul_mul_mul_comm, ← pow_add, hprodeq]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ hE) (pow_nonneg hb0 _)
    have hX0 : 0 ≤ (b⁻¹ * Pg.L ^ (31 * (Pg.d : ℝ) + 6)) ^ R := pow_nonneg (mul_nonneg (inv_nonneg.mpr hb0) hLe0) _
    have hLR : (withC₁ (PB Pg C) (frontierConst Pg.d ^ 16)).L ^ ((31 * (Pg.d : ℝ) + 6) * R) =
        (Pg.L ^ (31 * (Pg.d : ℝ) + 6)) ^ R := Real.rpow_mul_natCast hL0.le _ _
    have halg : ∀ {A B X F : ℝ}, 0 ≤ X → A * B ≤ F → A * X * B ≤ F * X := fun {A B X F} hX h => by
      calc A * X * B = (A * B) * X := by ring
        _ ≤ F * X := mul_le_mul_of_nonneg_right h hX
    rw [hLR]
    refine (halg hX0 hfac).trans (le_of_eq ?_)
    rw [mul_pow, inv_pow, pow_add, ← pow_mul]
    field_simp


end WaveTurbulence.Flower.MkSlots.IntAsm
