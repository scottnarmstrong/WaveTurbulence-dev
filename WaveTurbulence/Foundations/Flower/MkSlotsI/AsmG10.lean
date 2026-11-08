/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG9

/-! # B3s-HELPER7 AsmG (6): **`classRepGen_at_of`** — the general assembly at one parameter record

`MkSlotsG.ClassRepGen 452` at the record `withC₁ (PB Pg C) (liftGen Pg.d)`, from B3's gates at `Pg`, B3-2's V5W-2L class
bound and the top decay at `PB Pg C`, the general slot obligation `GenSlotObligationAt Kg (PB Pg C)`, the class
identity `ClassCentreIdentityAt Kg (PB Pg C)` (hypothesis; proved separately), `Cgen Pg.d Pg.η Pg.C₁ Kg ≤ C`, the
smallness `η ≤ 1/4` (the `X^{1/4}` slots pay the two hinge losses `2·6η⁶` and the selection moments `≤ 2/18`), and the
absorbed-selection bound `SelNativeBound` (`prod_selNative_le`, W:MkSlotsI/AsmG3.lean).

Adapted from α's `MkSlots.IntAsm.classRepAlphaJ_at` (W:MkSlots/IntAsm4.lean) and B3-2's
`MkUnitsL.vineCaseRepresentsFWMkL_of_gate` (W:MkUnitsL/AssemblyL.lean): HELPER9's engine
`MkSlotsE.representsIntMKSel_of_centreModes` (and `repMK_of_centreModes`) at the general piece `pieceGenAt … (mkU a.prime)`
(B3's unit marking `mkU a.prime = classMk mkF a`) with
* the domain `domOf π tt ∩ pinSet π.fix` (`hsliceD`: pinned points; `hval`: `outerValMμD_inter_pinSet`);
* the slot families `fam₀Of sd`, `famCOfData sd` of ClassForm's slot data (`exists_slotDataOK`), per-slot moment
  exponent `θs = 1/4` on `SelAdj` slots, `η` elsewhere, hinge exponent `c = 6η⁶`;
* the hinge data B3-2's `unit_hinge_dataWMkL` + `hHkPropD_pieceGenAt` (W:MkSlotsI/AsmG1.lean);
* the mass: slot/unit leaf products `≤ c_F^{16N} b^{N+R}` (B3), `|J| = R` cap slots carrying `b⁻¹`, the protected
  losses `≤ L^{(94d+10)|Π|}` (`prod_protLoss_le`), the `SelAdj` losses `≤ L^{4(47d+2)#sel}` (`prod_selAdj_le`), the
  selection constants `∏ selF ≤ 3^{4#sel}`, the class constant `‖sgnGen‖ ≤ ∏ Rs⁻¹ · chiDNorm^{#sel}`, the absorbed
  selections; the constants `c_F^{16N}`, `topFilterMass^{Σ|SU|}`, `81^{#sel}`, `chiDNorm^{#sel}` go into the `C₁` lift
  `liftGen^N`; the protected loss into `L^{452·d·nProt}` (`representsIntMKSel_absorb`, `representsIntMK_absorbG`).
The vine-free case (no unit) is included. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlotsI
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
  WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots.IntMember WaveTurbulence.Flower.MkSlots.IntCore
  WaveTurbulence.Flower.MkSlots.IntAsm
open WaveTurbulence.Flower.MkSlots (withC₁ recLG)
open WaveTurbulence.Flower.FinalMKDefs (RepresentsIntMKSel)
open scoped ENNReal Classical

/-- **`ClassRepGen 452` at one parameter record**, given the absorbed-selection bound and the class identity. -/
theorem classRepGen_at_of (hselN : SelNativeBound) (Pg : WTParams) (C : ℝ) (E : GateEnv Pg)
    (hη : 0 < Pg.η) (hη4 : Pg.η ≤ 1 / 4) (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM)
    (Kg : ℕ → ℝ → ℝ) (hC : Cgen Pg.d Pg.η Pg.C₁ Kg ≤ C)
    (hV : V5W2L.V5FrontierClassBoundAtL (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C))
    (hslot : GenSlotObligationAt Kg (PB Pg C)) (hid : ClassCentreIdentityAt Kg (PB Pg C)) :
    MkSlotsG.ClassRepGen 452 (withC₁ (PB Pg C) (liftGen Pg.d)) := by
  intro p hp R h1 h2 N hN1 hN2 J hJ pat kSel t ht s hs A hA hpl hTC roots h b Rf σ Rs dag hb hsn hRf hRs
    hhigh mkF hmk π hπ
  -- constants
  have hC1g : 1 ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hC)
  have hCg : Pg.C₁ ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hC)
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * max 1 (Kg Pg.d Pg.η)) ^ 2 * MkUnitsL.ChFWL Pg.d Pg.η ≤ C :=
    le_trans (le_max_right _ _) hC
  obtain ⟨hη6, hη1, hη12⟩ := eta_small_facts Pg.η hη E.hη
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
  have hN2' : N ≤ (PB Pg C).N (p + 1) ^ 4 := by rw [← N_withC₁ (PB Pg C) (liftGen Pg.d)]; exact hN2
  have h2' : R ≤ 10 * (PB Pg C).R (p + 1) := by rw [← R_withC₁ (PB Pg C) (liftGen Pg.d)]; exact h2
  have hA' : ∀ LG ∈ A, MkCarries (PB Pg C) p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p :=
    fun LG hLG => ⟨mkCarries_withC₁ (PB Pg C) _ (hA LG hLG).1, (hA LG hLG).2⟩
  have hp' : p < (PB Pg C).D := hp
  have hRs1 : ∀ j, 1 ≤ Rs j := fun j => hL1.trans (hRs j)
  -- the representative
  have haA : (repPt π).layered ∈ A := repPt_layered_memMk π
  have hcA := hA' (repPt π).layered haA
  have hcan : IsCanonGC (p + 1) (repPt π).layered := hcA.1.1
  have hordN : (repPt π).layered.garden.order = N := hcA.1.2.2.1
  have hirr : (repPt π).layered.garden.Irreducible := hcA.2.2.1
  have hGeo : CapGeo (repPt π).layered J p := hcA.2.2.2.2.1
  have hpatA : CapPatValid (repPt π).layered J pat p := hcA.2.2.2.2.2
  have hdec := (repPt π).prime.data.decoded_order (repPt π).prime.prime.1 (repPt π).prime.decodes
  have hsz : (repPt π).prime.data.size ≤ (PB Pg C).N (p + 1) ^ 4 := by omega
  have hMa := Mole.garden_isMolecule (repPt π).prime.skeleton
  have hplainA : (repPt π).layered.garden.IsPlain := by
    rw [← sourceLayer_reconstructs (repPt π)]; exact (repPt π).prime.data.garden_plain _
  have hroot := MkSlotsG.exists_capFlower_of_capGeo hGeo hplainA hirr (by rw [hJ])
  have hstemA : ¬ StemDep σ kSel ∨ CleanPt J (repPt π) :=
    hπ.imp id fun h => h (repPt π) (Relation.EqvGen.refl _)
  have hGeoA : CapGeo (layeredReconstruction (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
      (sourceLayer_isLayering (repPt π))) J p := by
    rw [sourceLayer_reconstructs (repPt π)]; exact hGeo
  -- the unit marking
  obtain ⟨mkU, hset, hout⟩ : ∃ mkU : Stage1Mk.MarkFn (2 * R), mkU (repPt π).prime = classMk mkF (repPt π) ∧
      (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkU =
        (repPt π).outputs (p := p) (kind := objKind (2 * R)) mkF :=
    ⟨fixMark (repPt π) (mkAt mkF (repPt π)), fixMark_self (repPt π) (mkAt mkF (repPt π)),
      outputs_fixMark_mkAt mkF (repPt π)⟩
  have hGplain : (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).G.IsPlain :=
    (stSt (repPt π).prime.skeleton (repPt π).totalSigma (mkU (repPt π).prime)).plain (repPt π).prime.prime.1
  -- the slot data and the class identity
  obtain ⟨sd, hsd⟩ := exists_slotDataOK hslot C le_rfl (repPt π) J pat t s hp' hcan hsz hJ hGeo hpatA hirr ht hs
    kSel hpl σ Rs hRs mkF hmk hstemA roots h b hb hsn Rf hRf hhigh dag (mkU (repPt π).prime) hset
  have hval0 := hid hd1 hL1 E.hη0 C p hp' R h1 h2' N hN1 hN2' J hJ pat kSel t ht s hs A hA' hpl hTC roots h b Rf σ
    Rs dag hb hsn hRf hRs hhigh mkF hmk π hπ mkU hset hout sd hsd
  have hordD : ((repPt π).prime.data.garden (repPt π).prime.prime.1).order = N := by
    rw [(repPt π).prime.gardenEq, hordN]
  have hnS : (repPt π).prime.skeleton.order ≤ N := by omega
  have hn : N - (repPt π).prime.skeleton.order = (repPt π).prime.data.size := by omega
  have hordg : ((repPt π).prime.data.garden (repPt π).prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
    rw [hordD]; exact hN2'
  have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
  have hC0 : (0 : ℝ) ≤ (PB Pg C).C₁ := le_trans zero_le_one hC1g
  -- the protected loss and the mass parameters
  have hℓle : genLossExp Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ) ≤
      452 * Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ) := by
    have hd' : (1 : ℝ) ≤ Pg.d := by exact_mod_cast hd1
    have hE : genLossExp Pg.d ≤ 452 * Pg.d := by unfold genLossExp; linarith
    exact mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg _)
  have hsm := selMassMK_le N hb0 Rs hRs1 kSel ((MkSlotsG.selRGen J kSel mkF (repPt π)).image fun v => v.1.1)
  have hlift1 := one_le_liftGen Pg.d
  have hlN0 : 0 ≤ liftGen Pg.d ^ N := pow_nonneg (by linarith) _
  have hLℓ0 : 0 ≤ Pg.L ^ (genLossExp Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ)) :=
    Real.rpow_nonneg hL0.le _
  -- the engine (both conclusions from the same data)
  have hboth : RepresentsIntMKSel (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag)
      (selRAt J kSel (repPt π) (mkU (repPt π).prime)) N 0 (fun _ => t) 0 roots
      (liftGen Pg.d ^ N * (Pg.L ^ (genLossExp Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ)) *
        selMassMK N b Rs kSel ((MkSlotsG.selRGen J kSel mkF (repPt π)).image fun v => v.1.1)))
      (classValue (PB Pg C) p J pat kSel t s A roots h Rf σ Rs dag mkF π) ∧
    (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag).RepresentsIntMK N (0 + 343)
      (fun _ => t) 0 roots
      (liftGen Pg.d ^ N * (Pg.L ^ (genLossExp Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ)) * b ^ N))
      (classValue (PB Pg C) p J pat kSel t s A roots h Rf σ Rs dag mkF π) := by
    refine ⟨MkSlotsE.representsIntMKSel_of_centreModes (P := PB Pg C) hd1 hL1 E.hη0
      (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag) hGplain (fun _ => t) 0 roots
      (selSkCMk (repPt π) mkU (PB Pg C).L (PB Pg C).γ (PB Pg C).η hL0.ne' 0 roots) ?hgsp
      (domOf (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag) (fun _ => t) ∩
        MkSlotsB.pinSet (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag).fix)
      ?hsliceD
      (pieceGenAt_filt_le (PB Pg C) J pat t s kSel σ Rs mkF (repPt π) dag hmk.sub hL1 hRs _ hset)
      (pieceGenAt_ind_mem (PB Pg C) J pat t s kSel σ Rs mkF (repPt π) dag _ hset) 0 le_rfl
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
      (selRAt J kSel (repPt π) (mkU (repPt π).prime))
      (selRAt_not_unitClock J pat t s kSel σ mkF (repPt π) hmk.sub hstemA _ hset)
      (fun _ : Unit => sgnGen J Pg.L Pg.γ Pg.δ s kSel Rs (repPt π) mkU roots dag)
      (fun _ => fam₀Of sd hsd.supp) (fun _ => famCOfData sd)
      (fun _ sl => μsGen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg b sl)
      (fun _ => unitKerGen (PB Pg C) p J σ kSel Rs (repPt π) mkU h Rf)
      (c := 6 * Pg.η ^ 6) (by positivity) hη1
      (θsGen (PB Pg C) J kSel (repPt π) (mkU (repPt π).prime))
      (hcθ_gen (PB Pg C) J kSel (repPt π) (mkU (repPt π).prime) hη hη4)
      (fun _ X sl => hμ_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg p σ roots h b Rf dag sd
        hsd X sl)
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) (max 1 (Kg Pg.d Pg.η)) (MkUnitsL.ChFWL Pg.d Pg.η) rfl
      (le_max_left _ _) (le_max_left _ _) hCχ
      (fun sl => slotSize (repPt π).prime.data (iotaAt (repPt π) (mkU (repPt π).prime) sl))
      (fun sl => slotIncoh (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π)) (iotaAt (repPt π) (mkU (repPt π).prime) sl))
      (fun _ sl => lfGen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) b sl)
      (fun _ sl => hlf_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) hL0.le hRs1 hb0 sl)
      (fun _ sl => hμb_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg hC0 hL0.le hRs1 hb0 sl)
      (fun _ j => M0Gen (PB Pg C) hM9 J σ kSel Rs (repPt π) mkU b j)
      (cl2Gen (repPt π) mkU) (gjGen (PB Pg C) hM9 (repPt π) mkU) (njGen hM9 (repPt π) mkU)
      (fun _ j => lfjGen (PB Pg C) J σ kSel Rs (repPt π) mkU b j)
      (fun _ j => hlfj_gen (PB Pg C) J σ kSel Rs (repPt π) mkU b j)
      (fun _ j => hM_gen (PB Pg C) hM9 J σ kSel Rs (repPt π) mkU b hC0 hL0.le j)
      (fun _ X ξ => hhinge_gen (PB Pg C) hV hM9 hgate hinc htop hd1 hη hη6 E.hη hC1g hδ hL1 hL2 hw hp' J pat t s
        kSel σ Rs hRs mkF hmk.sub (repPt π) hGeo hpatA hroot hs ht.2 dag mkU hset hcan hordg roots h b hb0 hsn Rf
        hRf _)
      N _ ?hs ?hexp ?hg ?hb ?hh ?hJ _ ?hval,
      MkSlotsE.repMK_of_centreModes (P := PB Pg C) hd1 hL1 E.hη0
      (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag) hGplain (fun _ => t) 0 roots
      (selSkCMk (repPt π) mkU (PB Pg C).L (PB Pg C).γ (PB Pg C).η hL0.ne' 0 roots) ?hgsp
      (domOf (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag) (fun _ => t) ∩
        MkSlotsB.pinSet (pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag).fix)
      ?hsliceD
      (pieceGenAt_filt_le (PB Pg C) J pat t s kSel σ Rs mkF (repPt π) dag hmk.sub hL1 hRs _ hset)
      (pieceGenAt_ind_mem (PB Pg C) J pat t s kSel σ Rs mkF (repPt π) dag _ hset) 0 le_rfl
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
      (selRAt J kSel (repPt π) (mkU (repPt π).prime))
      (selRAt_not_unitClock J pat t s kSel σ mkF (repPt π) hmk.sub hstemA _ hset)
      (fun _ : Unit => sgnGen J Pg.L Pg.γ Pg.δ s kSel Rs (repPt π) mkU roots dag)
      (fun _ => fam₀Of sd hsd.supp) (fun _ => famCOfData sd)
      (fun _ sl => μsGen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg b sl)
      (fun _ => unitKerGen (PB Pg C) p J σ kSel Rs (repPt π) mkU h Rf)
      (c := 6 * Pg.η ^ 6) (by positivity) hη1
      (θsGen (PB Pg C) J kSel (repPt π) (mkU (repPt π).prime))
      (hcθ_gen (PB Pg C) J kSel (repPt π) (mkU (repPt π).prime) hη hη4)
      (fun _ X sl => hμ_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg p σ roots h b Rf dag sd
        hsd X sl)
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) (max 1 (Kg Pg.d Pg.η)) (MkUnitsL.ChFWL Pg.d Pg.η) rfl
      (le_max_left _ _) (le_max_left _ _) hCχ
      (fun sl => slotSize (repPt π).prime.data (iotaAt (repPt π) (mkU (repPt π).prime) sl))
      (fun sl => slotIncoh (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π)) (iotaAt (repPt π) (mkU (repPt π).prime) sl))
      (fun _ sl => lfGen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) b sl)
      (fun _ sl => hlf_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) hL0.le hRs1 hb0 sl)
      (fun _ sl => hμb_gen (PB Pg C) J pat t s kSel Rs (repPt π) (mkU (repPt π).prime) Kg hC0 hL0.le hRs1 hb0 sl)
      (fun _ j => M0Gen (PB Pg C) hM9 J σ kSel Rs (repPt π) mkU b j)
      (cl2Gen (repPt π) mkU) (gjGen (PB Pg C) hM9 (repPt π) mkU) (njGen hM9 (repPt π) mkU)
      (fun _ j => lfjGen (PB Pg C) J σ kSel Rs (repPt π) mkU b j)
      (fun _ j => hlfj_gen (PB Pg C) J σ kSel Rs (repPt π) mkU b j)
      (fun _ j => hM_gen (PB Pg C) hM9 J σ kSel Rs (repPt π) mkU b hC0 hL0.le j)
      (fun _ X ξ => hhinge_gen (PB Pg C) hV hM9 hgate hinc htop hd1 hη hη6 E.hη hC1g hδ hL1 hL2 hw hp' J pat t s
        kSel σ Rs hRs mkF hmk.sub (repPt π) hGeo hpatA hroot hs ht.2 dag mkU hset hcan hordg roots h b hb0 hsn Rf
        hRf _)
      N _ ?hs ?hexp ?hg ?hb ?hh ?hJ _ ?hval
      _ ?hsb ?hLsel⟩
    case hgsp =>
      intro D' hD z
      exact normalizedPiece_gapIndicatorMk (repPt π) mkU D' hD hL0.ne' _ _ 0 roots z
    case hsliceD =>
      intro τ
      exact ⟨fun h => h.1, fun h => ⟨h, extendFix_mem_pinSet _ τ⟩⟩
    case hs =>
      rw [Fintype.sum_unique]
      exact hs_gen hselN (PB Pg C) hd1 hL1 J hJ pat t s kSel σ Rs hRs mkF hmk.sub (repPt π) hGeo hirr hordN mkU hset
        roots dag b hb
    case hexp =>
      exact exponent_order (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
        (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
        hGplain N hn hnS
    case hg =>
      have h1' := gsk_boundMk (stShape hMa (repPt π).totalSigma (mkU (repPt π).prime))
        (unitBlkMk_disj hMa (repPt π).totalSigma (mkU (repPt π).prime)) (repPt π).prime.data (repPt π).prime.prime.1
        hGplain (sourceLayer (repPt π)) (sourceLayer_isLayering (repPt π)) (repPt π).totalSigma
        (B₀ := sourceAssemblyMk (repPt π) mkU) (Mk := mkU (repPt π).prime) (hcov_unitsMk hMa (repPt π).totalSigma)
        (fun v => sourceLayer (repPt π) ((repPt π).prime.data.coreBranch (repPt π).prime.prime.1 v).toNode)
        (fun v => rfl)
      have h2'' := gsk_of_specMk (repPt π).prime.data (repPt π).prime.prime.1 (sourceLayer (repPt π))
        (sourceLayer_isLayering (repPt π)) (repPt π).layered (sourceLayer_reconstructs (repPt π))
        (repPt π).prime.decodes (repPt π).totalSigma (Mk := mkU (repPt π).prime)
      refine le_trans (le_of_eq h2'') (le_trans h1' (le_of_eq ?_))
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold gjGen
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
      exact hval0.trans (centreForm_inter_pinSet _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    case hsb =>
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsm.2 hLℓ0) hlN0
    case hLsel =>
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have hsc := selRAt_card_le (PB Pg C) J pat t s kSel σ Rs mkF (repPt π) dag _ hset
      have hsc' : ((selRAt J kSel (repPt π) (mkU (repPt π).prime)).card : ℝ) ≤
          ((pieceGenAt (PB Pg C) J pat t s kSel σ Rs (repPt π) (mkU (repPt π).prime) dag).nProt : ℝ) := by
        exact_mod_cast hsc
      have hd' : (1 : ℝ) ≤ Pg.d := by exact_mod_cast hd1
      have h7 : (7 : ℝ) * (47 * (Pg.d : ℝ) + 2) ≤ 343 * (Pg.d : ℝ) := by linarith
      exact le_trans (mul_le_mul_of_nonneg_left hsc' (by positivity))
        (mul_le_mul_of_nonneg_right h7 (Nat.cast_nonneg _))
  -- `C₁` lift, absorption of the protected loss, transport to the class marking
  obtain ⟨hrep1, hrep2⟩ := hboth
  refine ⟨?_, ?_⟩
  · have e1 := representsIntMKSel_C₁_lift _ _ (liftGen Pg.d) hlift1 hrep1
    have e2 := representsIntMKSel_absorb (P := withC₁ (PB Pg C) (liftGen Pg.d)) _ _ (cP₀ := 0) (cP := 452) hL1
      (by rw [zero_mul, zero_mul, zero_add]; exact hℓle) e1
    exact representsIntMKSel_pieceGenAt_congr (withC₁ (PB Pg C) (liftGen Pg.d)) J pat t s kSel σ Rs (repPt π) dag
      hset e2
  · have f1 := MkSlots.representsIntMK_C₁_lift _ (liftGen Pg.d) hlift1 hrep2
    have f2 := representsIntMK_absorbG (P := withC₁ (PB Pg C) (liftGen Pg.d)) _ (cP₀ := 0 + 343) (cP := 452 + 343)
      hL1 (by
        show (0 + 343 : ℝ) * (Pg.d : ℝ) * ((protI (repPt π).layered J pat t s kSel).card : ℝ) +
            genLossExp Pg.d * ((protI (repPt π).layered J pat t s kSel).card : ℝ) ≤
          (452 + 343) * (Pg.d : ℝ) * ((protI (repPt π).layered J pat t s kSel).card : ℝ)
        linarith [hℓle]) f1
    exact representsIntMK_pieceGenAt_congr (withC₁ (PB Pg C) (liftGen Pg.d)) J pat t s kSel σ Rs (repPt π) dag
      hset f2

end WaveTurbulence.Flower.MkSlotsI
