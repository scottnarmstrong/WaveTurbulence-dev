/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.CoupleRoot
public import WaveTurbulence.Foundations.Flower.FiltGate.TreeRoot
public import WaveTurbulence.Foundations.Flower.FiltSrc.Kernel
public import WaveTurbulence.Foundations.Flower.IncTop.StarTree
public import WaveTurbulence.Foundations.Flower.IncTop.StarCouple

/-! # D5b-3 FILT-GATE: the filtered star decays (`StarFiltCoupleDecay`, `StarFiltTreeDecay`)

Twins of INC-TOP's `Top/StarDecay` (`exists_KQstarStar_twoRoot_decay`, `exists_KQstarStar_oneRoot_decay`),
`StarCouple.exists_KQstarStar_decay` (root-shape dispatch) and `StarTree.exists_KTstarStar_decay` (copied by source,
sha256 in COPIED-SHA256SUMS), for the D5 multiplier `starWeight · filtWeight · filtWeight` at both gate weights:
- the kernel is the filtered weighted raw operator (D5b-1 `Kernel.lean`), with link multipliers
  `φ = coupleLinkFilt hQ F Fu ann M Mu` (trees `treeLinkFilt`), each `PresentedMult L (filtMomentConst ^ 4)` by D5a's
  `presentedMult_linkFiltWeight` (blocks of at most two branches, filter scales `≥ L`);
- the rates are `CoupleRoot`/`TreeRoot`'s, so the constant is `filtMomentConst ^ 4 · C₁`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.IncTop WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltLink
  WaveTurbulence.Flower.FiltProd

/-- Monotonicity of the filtered rate in its base constant. -/
theorem filtRate_mono_constant {C C' δ x y : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') (hδ : 0 ≤ δ) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (n : ℕ) :
    ENNReal.ofReal ((C * δ) ^ n * x * y) ≤ ENNReal.ofReal ((C' * δ) ^ n * x * y) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hC hδ) (mul_le_mul_of_nonneg_right hCC hδ) n) hx) hy)

/-- The couple link multipliers are presented at scale `L` with constant `filtMomentConst ^ 4`. -/
theorem presentedMult_coupleLinkFilt {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) {L : ℝ} (hL : 0 ≤ L)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ)
    (hM : ∀ b ∈ F, L ≤ M b) (hMu : ∀ b ∈ Fu, L ≤ Mu b) (j : Fin Q.links.length) :
    PresentedMult L (filtMomentConst ^ 4) (coupleLinkFilt hQ F Fu ann M Mu j) :=
  presentedMult_linkFiltWeight (coupleLinkBlock hQ j) F Fu ann M Mu hL (card_coupleLinkBlock_le hQ j) hM hMu

/-- The tree link multipliers are presented at scale `L` with constant `filtMomentConst ^ 4`. -/
theorem presentedMult_treeLinkFilt {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {L : ℝ} (hL : 0 ≤ L)
    (F Fu : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ)
    (hM : ∀ b ∈ F, L ≤ M b) (hMu : ∀ b ∈ Fu, L ≤ Mu b) (j : Fin (X.treeLinks (G.sig 0)).length) :
    PresentedMult L (filtMomentConst ^ 4) (treeLinkFilt hX F Fu ann M Mu j) :=
  presentedMult_linkFiltWeight (treeLinkBlock hX j) F Fu ann M Mu hL (card_treeLinkBlock_le hX j) hM hMu

theorem filtMomentConst_pow_pos : 0 < filtMomentConst ^ 4 :=
  pow_pos (zero_lt_one.trans_le one_le_filtMomentConst) 4

/-- Two branching roots. -/
theorem exists_KQstarFilt_twoRoot_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ H : LeafProfiles 2 d,
        (∀ ℓ ∈ inputLeaves LG.garden,
          Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
          (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) →
        ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
          (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
        ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
        Fourier.mixedRestrictionNorm θ (30 * d) (30 * d) (timeBox q q') univ
          (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
            coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) * L ^ c) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_rootRawCoupleKernel_rateFilt d hd B hB
  refine ⟨filtMomentConst ^ 4 * C₁, mul_pos filtMomentConst_pow_pos hC₁, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ hsmall (finiteLayerCutoff D)
    (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D) γ hγ hηγ δ hδ hδ₁
    ((D : ℝ) + 1) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL θ c hθc p hpD Q LG hQ hroots hlayers q q' hq hq' hrootq hrootq' hg H hH S ω cω hω F ann M hM Fu Mu
    hMu
  have hLone := hL₀.trans hL
  have hcount := coupleLayerLinks_incoherenceCount d hQ
  have hg' : 1 ≤ incoherenceCount (coupleLayerLinks (d := d) LG hQ) := hcount ▸ hg
  have hm : Fintype.card (PlusLeaf LG.garden) ≤ 3 * Q.links.length := by
    rw [coupleCarrier_input_count hQ]
    have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ) hg'
    omega
  have hspan (j) : |(((coupleLayerLinks (d := d) LG hQ j).leftLayer : ℝ)) -
      (coupleLayerLinks (d := d) LG hQ j).rightLayer| + 1 ≤ (D : ℝ) + 1 :=
    (coupleLayerLinks_span d hQ hlayers j).trans (by exact_mod_cast Nat.add_le_add_right hpD 1)
  let G := starRootMeasure (30 * d) S ω cω hω (coupleRow hQ)
  have hraw := hb L hL θ c hθc Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2 hm
    (coupleCarrier hQ) (coupleRootInputCoordinates hQ) (coupleCarrier_all_leaves hQ)
    (coupleLayerLinks LG hQ) hspan hg' (coupleRootCoordinates hQ hroots)
    (coupleInternalLinkDomain LG hQ) (measurableSet_coupleInternalLinkDomain hQ)
    (coupleInternalLinkDomain_subset_boxes d hQ) (filtMomentConst ^ 4) filtMomentConst_pow_pos
    (coupleLinkFilt hQ F Fu ann M Mu)
    (presentedMult_coupleLinkFilt hQ (zero_le_one.trans hLone) F Fu ann M Mu hM hMu)
    (coupleInputFunctionsL LG H) (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a)
    (timeBox q q') (timeBox_above_couple_roots d hQ hroots q q' hrootq hrootq')
    (finiteLayerCutoff_one_on_couple_box d D hQ hroots q q' (hq.trans hpD) (hq'.trans hpD))
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
      coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (MomentumTreeData.weightedSourceCoupleKernelFilt (P := (coupleCarrier hQ))) (G.at k.1)
        (gardenCircle LG.garden) (coupleRootCoordinates hQ hroots) L γ δ (coupleLayerLinks LG hQ)
        (coupleLinkFilt hQ F Fu ann M Mu) (coupleInternalLinkDomain LG hQ) (coupleInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact coupleLeavesW_starFilt_eq_weightedRaw hQ hroots L γ δ H k.1 ts.1 (30 * d) S ω cω hω F Fu ann M Mu
      (couple_lattice_summable hQ (by omega) L hLone H hB hH k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω cω hω (coupleRow hQ)

/-- One trivial tree (one branching root). -/
theorem exists_KQstarFilt_oneRoot_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        ∀ a : Fin 2, ([] : TTree.Path) ∈ (LG.garden.tree a).branching →
        (∀ b : GBranch LG.garden.tree, b.1.1 = a) →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ H : LeafProfiles 2 d,
        (∀ ℓ ∈ inputLeaves LG.garden,
          Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
          (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) →
        ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
          (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
        ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
        Fourier.mixedRestrictionNorm θ (30 * d) (30 * d) (timeBox q q') univ
          (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
            coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) * L ^ c) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_rootRawOneClockKernel_rateFilt d hd B hB
  refine ⟨filtMomentConst ^ 4 * C₁, mul_pos filtMomentConst_pow_pos hC₁, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ hsmall (finiteLayerCutoff D)
    (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D) γ hγ hηγ δ hδ hδ₁
    ((D : ℝ) + 1) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL θ c hθc p hpD Q LG hQ a hroot hwidth hlayers q q' hq hq' hrootq hrootq' hg H hH S ω cω hω F ann M hM
    Fu Mu hMu
  have hLone := hL₀.trans hL
  have hcount := coupleLayerLinks_incoherenceCount d hQ
  have hg' : 1 ≤ incoherenceCount (coupleLayerLinks (d := d) LG hQ) := hcount ▸ hg
  have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ) hg'
  have hm : Fintype.card (PlusLeaf LG.garden) ≤ 3 * Q.links.length := by
    rw [coupleCarrier_input_count hQ]
    omega
  have hspan (j) : |(((coupleLayerLinks (d := d) LG hQ j).leftLayer : ℝ)) -
      (coupleLayerLinks (d := d) LG hQ j).rightLayer| + 1 ≤ (D : ℝ) + 1 :=
    (coupleLayerLinks_span d hQ hlayers j).trans (by exact_mod_cast Nat.add_le_add_right hpD 1)
  let R := oneRootCoordinates hQ hn a hroot
  let b := passiveClockBase q q' a
  have hshift (t : Fin 2 → ℝ) (ht : t ∈ timeBox q q') :=
    R.oneClockShift_upper_bounds (coupleLayerLinks (d := d) LG hQ) a b t
      (timeBox_above_oneRoot d hQ hn a hroot q q' hrootq hrootq' ht)
      (fun j hj => (timeBox_passive_bounds q q' a ht j hj).1)
  have hbase : 0 ≤ R.baseRootTimes (coupleLayerLinks (d := d) LG hQ) a := by
    rw [oneRootCoordinates_base]
    exact Nat.cast_nonneg _
  have hχrect (t : Fin 2 → ℝ) (ht : t ∈ timeBox q q') :=
    R.finiteLayerCutoff_one_on_oneClock_rectangle (coupleLayerLinks (d := d) LG hQ) a b D t hbase
      (timeBox_clock_upper D q q' (hq.trans hpD) (hq'.trans hpD) ht a)
      (fun j hj => (timeBox_passive_bounds q q' a ht j hj).2)
  let G := starRootMeasure (30 * d) S ω cω hω (coupleRow hQ)
  have hraw := hb L hL θ c hθc Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2 hm
    (coupleCarrier hQ) (coupleRootInputCoordinates hQ) (coupleCarrier_all_leaves hQ)
    (coupleLayerLinks LG hQ) hspan hg' R a b
    (coupleInternalLinkDomain LG hQ) (measurableSet_coupleInternalLinkDomain hQ)
    (coupleInternalLinkDomain_subset_boxes d hQ) (filtMomentConst ^ 4) filtMomentConst_pow_pos
    (coupleLinkFilt hQ F Fu ann M Mu)
    (presentedMult_coupleLinkFilt hQ (zero_le_one.trans hLone) F Fu ann M Mu hM hMu)
    (coupleInputFunctionsL LG H) (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a)
    (timeBox q q') (fun t ht => (hshift t ht).1) (fun t ht => (hshift t ht).2) hχrect
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
      coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => weightedSourceOneClockKernelFilt (coupleCarrier hQ) (G.at k.1) (gardenCircle LG.garden) R a
        L γ δ (coupleLayerLinks LG hQ) (coupleLinkFilt hQ F Fu ann M Mu) (coupleInternalLinkDomain LG hQ)
        (coupleInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact coupleLeavesW_starFilt_eq_weightedOneClock hQ hn a hroot hwidth L γ δ H k.1 ts.1 (30 * d) S ω cω hω
      F Fu ann M Mu (couple_lattice_summable hQ (by omega) L hLone H hB hH k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω cω hω (coupleRow hQ)

/-- **Filtered star couple decay** (root-shape dispatch; weighted `exists_KQstarStar_decay`). -/
theorem starFiltCoupleDecay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) : StarFiltCoupleDecay d B := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := exists_KQstarFilt_twoRoot_decay d hd B hB
  obtain ⟨Cone, hCone, hone⟩ := exists_KQstarFilt_oneRoot_decay d hd B hB
  refine ⟨max Ctwo Cone, hCtwo.trans_le (le_max_left _ _), ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lt, hLt, htwo⟩ := htwo η hη (hη₁.trans (by norm_num)) hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨Lo, hLo, hone⟩ := hone η hη (hη₁.trans (by norm_num)) hsmall γ hγ hηγ δ hδ hδ₁ D
  refine ⟨max Lt Lo, hLt.trans (le_max_left _ _), ?_⟩
  intro L hL θ c hθc p hpD Q LG hQ hlayers q q' hq hq' hrootq hrootq' hg H hH S ω cω hω F ann M hM Fu Mu hMu
  have hLone : 1 ≤ L := hLt.trans ((le_max_left Lt Lo).trans hL)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hpos : 0 ≤ L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) :=
    Real.rpow_nonneg hL0 _
  have ht (hb : ∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) :=
    (htwo L ((le_max_left Lt Lo).trans hL) θ c hθc p hpD Q LG hQ hb hlayers q q' hq hq'
      hrootq hrootq' hg H hH S ω cω hω F ann M hM Fu Mu hMu).trans
      (mul_le_mul' le_rfl (filtRate_mono_constant hCtwo.le (le_max_left Ctwo Cone) hδ.le hpos
        (Real.rpow_nonneg hL0 c) Q.links.length))
  have ho (a : Fin 2) (hb : ([] : TTree.Path) ∈ (LG.garden.tree a).branching)
      (hw : ∀ b : GBranch LG.garden.tree, b.1.1 = a) :=
    (hone L ((le_max_right Lt Lo).trans hL) θ c hθc p hpD Q LG hQ a hb hw hlayers q q' hq hq'
      hrootq hrootq' hg H hH S ω cω hω F ann M hM Fu Mu hMu).trans
      (mul_le_mul' le_rfl (filtRate_mono_constant hCone.le (le_max_right Ctwo Cone) hδ.le hpos
        (Real.rpow_nonneg hL0 c) Q.links.length))
  by_cases h0 : ([] : TTree.Path) ∈ (LG.garden.tree 0).branching
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · exact ht (fun i => by fin_cases i <;> assumption)
    · apply ho 0 h0
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 1 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h1
  · by_cases h1 : ([] : TTree.Path) ∈ (LG.garden.tree 1).branching
    · apply ho 1 h1
      apply branch_index_eq_of_other_leaf
      intro i hi
      have he : i = 0 := by omega
      subst i
      exact tree_eq_leaf_of_root_not_branching h0
    · have hn := one_le_linkCount_of_incoherent (coupleLayerLinks (d := d) LG hQ)
        ((coupleLayerLinks_incoherenceCount d hQ).symm ▸ hg)
      let b := chosenBranch hQ (⟨0, by omega⟩ : Fin Q.links.length)
      have hr := root_mem_branching_of_mem b.2
      by_cases hb : b.1.1 = 0
      · rw [hb] at hr
        exact False.elim (h0 hr)
      · have hb1 : b.1.1 = 1 := by omega
        rw [hb1] at hr
        exact False.elim (h1 hr)

/-- **Filtered star tree decay** (weighted `exists_KTstarStar_decay`). -/
theorem starFiltTreeDecay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) : StarFiltTreeDecay d B := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_rootRawTreeKernel_rateFilt d hd B hB
  refine ⟨filtMomentConst ^ 4 * C₁, mul_pos filtMomentConst_pow_pos hC₁, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  choose L₀ hL₀ hb using fun l : Fin 3 => hb l (by omega) η hη hη₁ hsmall
    (finiteLayerCutoff D) (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D)
    γ hγ hηγ δ hδ hδ₁ ((D : ℝ) + 1) (by positivity)
  let Lstar := max (L₀ 0) (max (L₀ 1) (L₀ 2))
  have hmax (l : Fin 3) : L₀ l ≤ Lstar := by
    fin_cases l
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Lstar, (hL₀ 0).trans (hmax 0), ?_⟩
  intro L hL θ c hθc p hpD X LG hX hlayers q q' hq hq' hg H hH S ω cω hω F ann M hM Fu Mu hMu
  have hcount := treeLayerLinks_incoherenceCount d hX
  have hg' : 1 ≤ incoherenceCount (treeLayerLinks (d := d) LG hX) := hcount ▸ hg
  have hn := one_le_linkCount_of_incoherent (treeLayerLinks (d := d) LG hX) hg'
  have hnontriv : X ≠ .nil := by
    intro he
    subst X
    simp [RegChain.treeLinks, RegChain.linksAt] at hn
  let Csel := actualTreeSelection hX hnontriv
  have hmsel : Csel.m ≤ 2 := by rcases Csel.m_cases with h | h <;> omega
  let l : Fin 3 := ⟨Csel.m, by omega⟩
  have hLa := (hmax l).trans hL
  have hLone := (hL₀ l).trans hLa
  have hm : Fintype.card (TPlus LG.garden) + 1 ≤ 3 * (X.treeLinks (LG.garden.sig 0)).length := by
    rw [tree_input_count hX]
    omega
  have hspan (j) : |(((treeLayerLinks (d := d) LG hX j).leftLayer : ℝ)) -
      (treeLayerLinks (d := d) LG hX j).rightLayer| + 1 ≤ (D : ℝ) + 1 :=
    (treeLayerLinks_span d hX hlayers j).trans (by exact_mod_cast Nat.add_le_add_right hpD 1)
  let G := starRootMeasure (30 * d) S ω cω hω (treeRow hX)
  have hraw := hb l L hLa θ c hθc (X.treeLinks (LG.garden.sig 0)).length (Fintype.card (TPlus LG.garden)) 1 hm
    (treeCarrier hX) (treeLayerLinks LG hX) hspan hg' Csel.rootCoordinates
    (actualTreeFibers LG hX Csel) Csel.rootCoordinates_first Csel.rootCoordinates_last
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD) Csel.rootCoordinates)
    (finiteLayerCutoff_one_on_tree_clocks D LG hX (fun a => (hlayers a).trans hpD)
      Csel.selection.coordinates)
    (filtMomentConst ^ 4) filtMomentConst_pow_pos (treeLinkFilt hX F Fu ann M Mu)
    (presentedMult_treeLinkFilt hX (zero_le_one.trans hLone) F Fu ann M Mu hM hMu)
    (treeInputFunctionsL LG H) (fun a => treeInputFunctions_spatialNorm_leL hX H hH a)
    (timeBoxGt q q') (fun _ ht => ht.2.le)
    (finiteLayerCutoff_one_on_timeBoxGt D q q' (hq.trans hpD) (hq'.trans hpD))
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBoxGt q q') (k : (univ : Set (Mom d))) =>
      treeLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (MomentumTreeData.weightedSourceTreeKernelFilt (P := treeCarrier hX)) (G.at k.1)
        (gardenCircle LG.garden) Csel.rootCoordinates L γ δ (treeLayerLinks LG hX) (treeLinkFilt hX F Fu ann M Mu)
        (actualTreeFibers (d := d) LG hX Csel).timeDomain (treeInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact treeLeavesW_starFilt_eq_weightedRaw hX Csel L γ δ H k.1 ts.1 (30 * d) S ω cω hω F Fu ann M Mu
      ((treeCarrier hX).summable_norm_treeSourceLeafWeight_lattice (by omega)
        (treeInputFunctionsL LG H) hLone (by omega) (by omega)
        (fun a => treeInputFunctions_spatialNorm_leL hX H hH a) k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω cω hω (treeRow hX)

end WaveTurbulence.Flower.FiltGate
