/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG8

/-! # B3s-HELPER7 AsmG (5): **`hs_gen`** — the mass hypothesis of the engine in `classRepGen_at`

`‖sgnGen‖ · (∏_t selF t · lfGen t) · ∏_j lfjGen j ≤ L^{7(47d+2)#sel} · liftGen^N · L^{(94d+10)|Π|} · selMassMK`:
* `‖sgnGen‖ ≤ ∏_{kSel j} Rs_j⁻¹ · chiDNorm^{#sel}` (`norm_sgnGen_le`); if the selection test fails, `sgnGen = 0`;
* `∏ selF ≤ 3^{4#sel}` (`prod_selF_le`);
* the leaf factors: `∏_t c_F^{nr} genLeaf · ∏_j topFilterMass^{|SU j|} c_F^{…} regionLeafSize ≤
  c_F^{16N} topFilterMass^{2N} b^N` (B3's `weight_exponent_le`, `leaf_prod_split`; `|J| = R` cap slots with `b⁻¹`,
  `genLeaf_iota`, `prod_capSlot`; `|SU j| ≤ 2`, at most `N` units);
* the protected losses `≤ L^{(94d+10)|Π|}` (`prod_protLoss_le`);
* the selected-native gains `≤ ∏_{absorbed j} Rs_j^{-1/18}` (`SelNativeBound`);
* the `SelAdj` losses `≤ L^{4(47d+2)#sel} ≤ L^{7(47d+2)#sel}` (`prod_selAdj_le`);
* `chiDNorm^{#sel} · 3^{4#sel} · c_F^{16N} · topFilterMass^{2N} ≤ liftGen^N` (`#sel ≤ N`). -/

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
open WaveTurbulence.Flower.MkSlots.IntMember WaveTurbulence.Flower.MkSlots.IntAsm
open WaveTurbulence.Flower.MkSlots (withC₁ recLG)
open scoped ENNReal Classical

/-- **The leaf part of the mass**: `∏ c_F^{nr} · ∏ genLeaf · ∏ topFilterMass^{|SU|} · ∏ (c_F^{…} regionLeafSize) ≤
c_F^{16N} · topFilterMass^{2N} · b^N`. -/
theorem leaf_mass_le (P : WTParams) {p R N : ℕ} (J : Finset (Fin (2 * R))) (hJ : J.card = R)
    (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
    (hGeo : CapGeo a.layered J p) (hirr : a.layered.garden.Irreducible) (hordN : a.layered.garden.order = N)
    (mk : Stage1Mk.MarkFn (2 * R)) (b : ℝ) (hb : 1 ≤ b) :
    (∏ sl, frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (iotaAt a (mk a.prime) sl)) *
      (∏ sl, genLeaf a J b (iotaAt a (mk a.prime) sl)) *
      ((∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length) *
        ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
            (mk a.prime) j).atoms.card + 4 * clLocalOrder2 a.prime.data a.prime.prime.1
            (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j))) *
          regionLeafSize a.prime.data a.prime.prime.1
            (regionOf (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j))
            (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ)))) ≤
      (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) * b ^ N := by
  have hb0 : 0 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hcψ : 1 ≤ frontierConst P.d := one_le_frontierConst _
  have hc0 : 0 ≤ frontierConst P.d := by linarith
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hGplain : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain :=
    (stSt a.prime.skeleton a.totalSigma (mk a.prime)).plain a.prime.prime.1
  have hdec := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hordD : (a.prime.data.garden a.prime.prime.1).order = N := by rw [a.prime.gardenEq, hordN]
  have hnS : a.prime.skeleton.order ≤ N := by omega
  have hn : N - a.prime.skeleton.order = a.prime.data.size := by omega
  have hGsbN : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.order ≤ N := by
    have h3 := order_add_hinges_leMk (Mk := mk a.prime) hMa a.totalSigma
    omega
  have hunits : Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) ≤ N :=
    (card_units_le_order (stShape hMa a.totalSigma (mk a.prime)) (unitBlkMk_disj hMa a.totalSigma (mk a.prime))).trans
      hGsbN
  -- cap slots
  have hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a)) J p := by
    rw [sourceLayer_reconstructs a]; exact hGeo
  have hcapG : ∀ j ∈ J, (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree j = TTree.leaf := fun j hj =>
    shape_tree_leaf (stShape hMa a.totalSigma (mk a.prime))
      (skel_tree_leaf a.prime.data a.prime.prime.1 (hGeoA.cap_leaf j hj))
  have hGirr : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.Irreducible :=
    (stSt a.prime.skeleton a.totalSigma (mk a.prime)).irred a.prime.prime.1 (skeleton_irreducible a.prime hirr)
  have hccG := no_capcap_of_irred _ hGplain hGirr J hJ hcapG
  have hgl : ∏ sl, genLeaf a J b (iotaAt a (mk a.prime) sl) =
      b⁻¹ ^ R * ∏ sl, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) (iotaAt a (mk a.prime) sl) := by
    rw [Finset.prod_congr rfl fun sl _ => genLeaf_iota a J b (mk a.prime) sl, Finset.prod_mul_distrib,
      prod_capSlot _ hGplain J hcapG hccG, hJ]
  -- B3's leaf products
  have hexpo := weight_exponent_le (stShape hMa a.totalSigma (mk a.prime)) (unitBlkMk_disj hMa a.totalSigma (mk a.prime))
    a.prime.data a.prime.prime.1 hGplain N hn hnS
  have hE : (∑ s', Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
        ((stShape hMa a.totalSigma (mk a.prime)).iota a.prime.prime.1 hGplain s')) +
      ∑ j, (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) ≤
        16 * N := by
    rw [hordD] at hexpo; omega
  have hplainA : a.layered.garden.IsPlain := by
    rw [← sourceLayer_reconstructs a]; exact a.prime.data.garden_plain _
  have hprodeq : (∏ t, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) ((stShape hMa a.totalSigma (mk a.prime)).iota a.prime.prime.1 hGplain t)) *
      ∏ j, regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
        (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ)) = b ^ (N + R) := by
    rw [leaf_prod_split (stShape hMa a.totalSigma (mk a.prime)) (unitBlkMk_disj hMa a.totalSigma (mk a.prime))
      a.prime.data a.prime.prime.1 hGplain (sourceLayer a) (sourceLayer_isLayering a) b.toNNReal,
      sourceLayer_reconstructs]
    exact leafSizeProduct_const a.layered hplainA hordN b hb0
  have hfac : (∏ t, (frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
          ((stShape hMa a.totalSigma (mk a.prime)).iota a.prime.prime.1 hGplain t) *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => b.toNNReal)
          ((stShape hMa a.totalSigma (mk a.prime)).iota a.prime.prime.1 hGplain t))) *
      ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) *
        regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
          (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ))) ≤
      frontierConst P.d ^ (16 * N) * b ^ (N + R) := by
    rw [prod_pow_mul_prod, prod_pow_mul_prod, mul_mul_mul_comm, ← pow_add, hprodeq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ hE) (pow_nonneg hb0 _)
  -- the top filters
  have hTf : ∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length ≤ topFilterMass ^ (2 * N) := by
    rw [Finset.prod_pow_eq_pow_sum]
    refine pow_le_pow_right₀ V5WB.one_le_topFilterMass ?_
    have hlen : ∀ j, (SUGen P J σ kSel Rs a mk j).length ≤ 2 := by
      intro j
      unfold SUGen MkSlotsT.SURep MkSlotsT.SUStem
      split_ifs
      · exact length_radTGen_le _ _ _ _ _
      · simp
    calc ∑ j, (SUGen P J σ kSel Rs a mk j).length ≤ ∑ _j : Fin (unitBlocks a.prime.skeleton a.totalSigma
          (mk a.prime)).length, 2 := Finset.sum_le_sum fun j _ => hlen j
      _ = 2 * Fintype.card (Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ 2 * N := by omega
  -- assemble
  have hSL0 : 0 ≤ ∏ sl, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (iotaAt a (mk a.prime) sl) := Finset.prod_nonneg fun sl _ => slotLeaf_nonneg _ _ _ _ _ _
  have hA20 : 0 ≤ ∏ sl, frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
      (iotaAt a (mk a.prime) sl) := Finset.prod_nonneg fun sl _ => pow_nonneg hc0 _
  have hUU0 : 0 ≤ ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) *
        regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
          (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ))) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (pow_nonneg hc0 _)
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
  have hTf0 : 0 ≤ ∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length :=
    Finset.prod_nonneg fun j _ => pow_nonneg topFilterMass_nonneg _
  rw [hgl]
  have e1 : (∏ sl, frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (iotaAt a (mk a.prime) sl)) *
      (b⁻¹ ^ R * ∏ sl, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        (fun _ => b.toNNReal) (iotaAt a (mk a.prime) sl)) *
      ((∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length) *
        ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
          4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) *
          regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
            (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ)))) =
      (b⁻¹ ^ R * ∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length) *
        ((∏ sl, frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (iotaAt a (mk a.prime) sl)) *
          (∏ sl, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (iotaAt a (mk a.prime) sl)) *
        ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
          4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) *
          regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
            (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ)))) := by
    ring
  rw [e1]
  have hbR0 : 0 ≤ b⁻¹ ^ R := pow_nonneg (inv_nonneg.2 hb0) _
  calc _ ≤ (b⁻¹ ^ R * topFilterMass ^ (2 * N)) * (frontierConst P.d ^ (16 * N) * b ^ (N + R)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTf hbR0) (by rw [← Finset.prod_mul_distrib]; exact hfac)
          (mul_nonneg (mul_nonneg hA20 hSL0) hUU0)
          (mul_nonneg hbR0 (pow_nonneg topFilterMass_nonneg _))
    _ = (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) * b ^ N := by
        rw [pow_add, inv_pow]
        field_simp

/-- **The mass hypothesis `hs` of the engine** (one class term). -/
theorem hs_gen (hselN : SelNativeBound) (P : WTParams) (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L) {p R N : ℕ}
    (J : Finset (Fin (2 * R))) (hJ : J.card = R) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
    (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (hGeo : CapGeo a.layered J p) (hirr : a.layered.garden.Irreducible)
    (hordN : a.layered.garden.order = N) (mk : Stage1Mk.MarkFn (2 * R)) (hset : mk a.prime = classMk mkF a)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (b : ℝ) (hb : 1 ≤ b) :
    ‖sgnGen J P.L P.γ P.δ s kSel Rs a mk roots dag‖ *
      ((∏ sl, MkSlotsS.selF ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route
          a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).plain a.prime.prime.1))
          (selRAt J kSel a (mk a.prime)) sl * lfGen P J pat t s kSel Rs a (mk a.prime) b sl) *
        ∏ j, lfjGen P J σ kSel Rs a mk b j) ≤
      P.L ^ (7 * (47 * (P.d : ℝ) + 2) * ((selRAt J kSel a (mk a.prime)).card : ℝ)) *
        (liftGen P.d ^ N * (P.L ^ (genLossExp P.d * ((protI a.layered J pat t s kSel).card : ℝ)) *
          selMassMK N b Rs kSel ((selRAt J kSel a (classMk mkF a)).image fun v => v.1.1))) := by
  have hL0 : 0 < P.L := lt_of_lt_of_le zero_lt_one hL1
  have hb0 : 0 ≤ b := by linarith
  have hRs1 : ∀ j, 1 ≤ Rs j := fun j => hL1.trans (hRs j)
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  have hGplain : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain :=
    (stSt a.prime.skeleton a.totalSigma (mk a.prime)).plain a.prime.prime.1
  have hLe1 : 1 ≤ P.L ^ (47 * (P.d : ℝ) + 2) := Real.one_le_rpow hL1 (by positivity)
  have hlift1 := one_le_liftGen P.d
  have hsm := selMassMK_le N hb0 Rs hRs1 kSel ((selRAt J kSel a (classMk mkF a)).image fun v => v.1.1)
  -- `#sel ≤ N`
  have hdec := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hordD : (a.prime.data.garden a.prime.prime.1).order = N := by rw [a.prime.gardenEq, hordN]
  have hnS : a.prime.skeleton.order ≤ N := by omega
  have hGsbN : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.order ≤ N := by
    have h3 := order_add_hinges_leMk (Mk := mk a.prime) hMa a.totalSigma
    omega
  have hselcard : (selRAt J kSel a (mk a.prime)).card ≤ N := by
    have h1' := Finset.card_le_univ (selRAt J kSel a (mk a.prime))
    rw [← RedSplice.Garden_order_eq_card] at h1'
    omega
  -- the selection test
  by_cases hok : ∀ j, (kSel j).isSome → (selCap (recLG a) J kSel j).isSome
  swap
  · have hso : selOK (recLG a) J kSel = 0 := by
      unfold selOK
      exact ite_eq_right_iff.2 fun h' => absurd h' hok
    have h0 : sgnGen J P.L P.γ P.δ s kSel Rs a mk roots dag = 0 := by
      unfold sgnGen
      rw [hso]
      simp
    rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg hL0.le _) (mul_nonneg (pow_nonneg (by linarith) _)
      (mul_nonneg (Real.rpow_nonneg hL0.le _) hsm.1))
  -- the factors
  have hsg := norm_sgnGen_le J P.L P.γ P.δ s kSel Rs (fun j => lt_of_lt_of_le one_pos (hRs1 j)) a mk roots dag
  have hA1 := prod_selF_le hGplain ((stShape hMa a.totalSigma (mk a.prime)).route a.prime.prime.1 hGplain)
    (selRAt J kSel a (mk a.prime))
    (fun sl i => (stShape hMa a.totalSigma (mk a.prime)).route_natural a.prime.prime.1 hGplain sl i)
  have h23 := leaf_mass_le P J hJ σ kSel Rs a hGeo hirr hordN mk b hb
  have hA4 := prod_protLoss_le (d := P.d) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (stShape hMa a.totalSigma (mk a.prime)) hGplain (protI (recLG a) J pat t s kSel) hL1
  have hcard : ((protI (recLG a) J pat t s kSel).card : ℝ) = ((protI a.layered J pat t s kSel).card : ℝ) :=
    congrArg (fun LG : LayeredGarden (2 * R) => ((protI LG J pat t s kSel).card : ℝ)) (sourceLayer_reconstructs a)
  rw [hcard] at hA4
  have hA5 := hselN J pat t s kSel Rs mkF hsub a (mk a.prime) hset hRs1 hok
  rw [selRAt_image_congr J kSel a hset] at hA5
  have hA6 := prod_selAdj_le pat t s kSel mkF hsub a (mk a.prime) hset hLe1
  have h67 : (P.L ^ (47 * (P.d : ℝ) + 2)) ^ (4 * (selRAt J kSel a (mk a.prime)).card) ≤
      P.L ^ (7 * (47 * (P.d : ℝ) + 2) * ((selRAt J kSel a (mk a.prime)).card : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    push_cast
    have : (0 : ℝ) ≤ (47 * (P.d : ℝ) + 2) * ((selRAt J kSel a (mk a.prime)).card : ℝ) := by positivity
    nlinarith
  have hlift : chiDNorm ^ (selRAt J kSel a (mk a.prime)).card * 3 ^ (4 * (selRAt J kSel a (mk a.prime)).card) *
      (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) ≤ liftGen P.d ^ N := by
    have e : liftGen P.d ^ N = (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) *
        ((81 : ℝ) ^ N * chiDNorm ^ N) := by
      unfold liftGen
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      ring
    rw [e]
    have h81 : (3 : ℝ) ^ (4 * (selRAt J kSel a (mk a.prime)).card) ≤ 81 ^ N := by
      rw [pow_mul]
      norm_num
      exact pow_le_pow_right₀ (by norm_num) hselcard
    have hχ : chiDNorm ^ (selRAt J kSel a (mk a.prime)).card ≤ chiDNorm ^ N :=
      pow_le_pow_right₀ one_le_chiDNorm hselcard
    have hM0 : 0 ≤ frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N) :=
      mul_nonneg (pow_nonneg (le_trans zero_le_one (one_le_frontierConst _)) _) (pow_nonneg topFilterMass_nonneg _)
    calc chiDNorm ^ (selRAt J kSel a (mk a.prime)).card * 3 ^ (4 * (selRAt J kSel a (mk a.prime)).card) *
          (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) =
          (frontierConst P.d ^ (16 * N) * topFilterMass ^ (2 * N)) *
            (3 ^ (4 * (selRAt J kSel a (mk a.prime)).card) * chiDNorm ^ (selRAt J kSel a (mk a.prime)).card) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul h81 hχ (pow_nonneg chiDNorm_pos.le _) (by positivity)) hM0
  -- distribute the products
  have hP1 : ∏ sl, MkSlotsS.selF ((stShape hMa a.totalSigma (mk a.prime)).route a.prime.prime.1 hGplain)
        (selRAt J kSel a (mk a.prime)) sl * lfGen P J pat t s kSel Rs a (mk a.prime) b sl =
      (∏ sl, MkSlotsS.selF ((stShape hMa a.totalSigma (mk a.prime)).route a.prime.prime.1 hGplain)
        (selRAt J kSel a (mk a.prime)) sl) *
      ((∏ sl, frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (iotaAt a (mk a.prime) sl)) *
        (∏ sl, genLeaf a J b (iotaAt a (mk a.prime) sl)) *
        (∏ sl, P.L ^ (if HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (protI (recLG a) J pat t s kSel) (iotaAt a (mk a.prime) sl) then genLossExp P.d else 0)) *
        (∏ sl, ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
          kSel (iotaAt a (mk a.prime) sl), Rs v.1.1 ^ (-(1 / 18 : ℝ))) *
        (∏ sl, (if SelAdjO J kSel a (mk a.prime) sl then P.L ^ (47 * (P.d : ℝ) + 2) else 1))) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    unfold lfGen
    simp only [Finset.prod_mul_distrib]
  have hP2 : ∏ j, lfjGen P J σ kSel Rs a mk b j =
      (∏ j, topFilterMass ^ (SUGen P J σ kSel Rs a mk j).length) *
        ∏ j, (frontierConst P.d ^ (9 * (unitBlkMk hMa a.totalSigma (mk a.prime) j).atoms.card +
          4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))) *
          regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlkMk hMa a.totalSigma (mk a.prime) j))
            (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((b.toNNReal : NNReal) : ℝ))) := by
    unfold lfjGen
    exact Finset.prod_mul_distrib
  rw [hP1, hP2, selMassMK_eq]
  have hQ10 : 0 ≤ ∏ j, (if (kSel j).isSome then (Rs j)⁻¹ else 1 : ℝ) :=
    Finset.prod_nonneg fun j _ => by
      split_ifs
      · exact inv_nonneg.2 (le_trans zero_le_one (hRs1 j))
      · exact zero_le_one
  have hQ20 : 0 ≤ ∏ j, (if (kSel j).isSome ∧ j ∉ (selRAt J kSel a (classMk mkF a)).image (fun v => v.1.1) then
      Rs j ^ (-(1 / 18 : ℝ)) else 1) :=
    Finset.prod_nonneg fun j _ => by
      split_ifs
      · exact Real.rpow_nonneg (le_trans zero_le_one (hRs1 j)) _
      · exact zero_le_one
  have hc0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst _)
  exact hs_arith (norm_nonneg _) hsg hQ10 (pow_nonneg chiDNorm_pos.le _)
    (Finset.prod_nonneg fun sl _ => MkSlotsS.selF_nonneg _ _ sl) hA1 (by positivity)
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun sl _ => pow_nonneg hc0 _)
      (Finset.prod_nonneg fun sl _ => genLeaf_nonneg a J hb0 _))
      (mul_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg topFilterMass_nonneg _)
        (Finset.prod_nonneg fun j _ => mul_nonneg (pow_nonneg hc0 _)
          (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)))))
    h23 (mul_nonneg (pow_nonneg hc0 _) (pow_nonneg topFilterMass_nonneg _)) (pow_nonneg hb0 _)
    (Finset.prod_nonneg fun sl _ => Real.rpow_nonneg hL0.le _) hA4
    (Finset.prod_nonneg fun sl _ => Finset.prod_nonneg fun v _ => Real.rpow_nonneg (le_trans zero_le_one
      (hRs1 _)) _) hA5
    (Finset.prod_nonneg fun sl _ => by split_ifs <;> linarith) hA6 h67
    (Real.rpow_nonneg hL0.le _) hQ20 (pow_nonneg (by linarith) _) hlift

end WaveTurbulence.Flower.MkSlotsI
