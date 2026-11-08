/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.TopIdentity
public import WaveTurbulence.Foundations.Flower.IncTop.Top.GardenPresentation
public import WaveTurbulence.Foundations.Flower.IncTop.Top.CoupleRootRate
public import WaveTurbulence.Foundations.Flower.IncTop.Top.TreeRootRate
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.AllCoupleDecay
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeDecay

/-! Ported by source from C2-B-TOP `C2BTop.StarDecay` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Star-weighted Proposition 5.1 for decoded couples and paired trees (restriction form)

Weighted copies of main's `exists_KQstar_twoRoot_decayL`, `exists_KQstar_oneRoot_decayL`,
`exists_KQstar_decayL` and `exists_KTstar_decayL`: the star-weighted leafwise kernels are the
root-modulated weighted raw operators (`TopIdentity`, `GardenPresentation`), bounded by
`exists_rootRaw…_rate`; the presentation cost is `rootJetConstant (30d) * ∏_{a ∈ S} c a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.Stage1W

theorem couple_lattice_summable {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 1 ≤ L) (H : LeafProfiles 2 d) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden,
      Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) (k : Mom d) :
    Summable (fun p : Fin Q.links.length × Fin 2 → Fin d → ℤ =>
      ‖(coupleCarrier hQ).sourceLeafWeight (coupleInputFunctionsL LG H) k
        (fun i j => latticePoint L (p (i, j)))‖) := by
  obtain ⟨C, _, hloc⟩ := exists_uniform_couple_link_cell_localization d hd
  choose S hScard hcover using fun c => hloc Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2
    (coupleCarrier hQ) (coupleCarrier_all_leaves hQ) c
  exact (coupleCarrier hQ).summable_norm_sourceLeafWeight_lattice (coupleInputFunctionsL LG H) S hcover
    hScard hL (by omega) (by omega) hB (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a) k

/-- Two branching roots. -/
theorem exists_KQstarStar_twoRoot_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
        ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ i, ([] : TTree.Path) ∈ (LG.garden.tree i).branching) →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links → ∀ H : LeafProfiles 2 d,
        (∀ ℓ ∈ inputLeaves LG.garden,
          Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
        ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
          (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (c a)) →
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox q q') univ
          (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
            coupleLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootRawCoupleKernel_rate d hd B hB
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ hsmall (finiteLayerCutoff D)
    (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D) γ hγ hηγ δ hδ hδ₁
    ((D : ℝ) + 1) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL p hpD Q LG hQ hroots hlayers q q' hq hq' hrootq hrootq' hg H hH S ω c hω
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
  let G := starRootMeasure (30 * d) S ω c hω (coupleRow hQ)
  have hraw := hb L hL Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2 hm
    (coupleCarrier hQ) (coupleRootInputCoordinates hQ) (coupleCarrier_all_leaves hQ)
    (coupleLayerLinks LG hQ) hspan hg' (coupleRootCoordinates hQ hroots)
    (coupleInternalLinkDomain LG hQ) (measurableSet_coupleInternalLinkDomain hQ)
    (coupleInternalLinkDomain_subset_boxes d hQ) (coupleInputFunctionsL LG H)
    (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a)
    (timeBox q q') (timeBox_above_couple_roots d hQ hroots q q' hrootq hrootq')
    (finiteLayerCutoff_one_on_couple_box d D hQ hroots q q' (hq.trans hpD) (hq'.trans hpD))
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
      coupleLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (MomentumTreeData.weightedSourceCoupleKernel (P := (coupleCarrier hQ))) (G.at k.1) (gardenCircle LG.garden)
        (coupleRootCoordinates hQ hroots) L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ)
        (coupleInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact coupleLeavesW_eq_weightedRaw_of_summable hQ hroots L γ δ H k.1 ts.1 (starWeight S ω) (G.at k.1)
      (couple_starWeight_eq_value hQ (30 * d) S ω c hω L k.1)
      (couple_lattice_summable hQ (by omega) L hLone H hB hH k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω c hω (coupleRow hQ)

/-- One trivial tree (one branching root). -/
theorem exists_KQstarStar_oneRoot_decay (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ p : ℕ, p ≤ D →
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
          (c : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (c a)) →
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox q q') univ
          (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
            coupleLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) ≤
            ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
            ENNReal.ofReal ((C * δ) ^ Q.links.length *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)) := by
  obtain ⟨C, hC, hb⟩ := exists_rootRawOneClockKernel_rate d hd B hB
  refine ⟨C, hC, ?_⟩
  intro η hη hη₁ hsmall γ hγ hηγ δ hδ hδ₁ D
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ hsmall (finiteLayerCutoff D)
    (contDiff_finiteLayerCutoff D) (hasCompactSupport_finiteLayerCutoff D) γ hγ hηγ δ hδ hδ₁
    ((D : ℝ) + 1) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL p hpD Q LG hQ a hroot hwidth hlayers q q' hq hq' hrootq hrootq' hg H hH S ω c hω
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
  let G := starRootMeasure (30 * d) S ω c hω (coupleRow hQ)
  have hraw := hb L hL Q.links.length (Fintype.card (PlusLeaf LG.garden)) 2 hm
    (coupleCarrier hQ) (coupleRootInputCoordinates hQ) (coupleCarrier_all_leaves hQ)
    (coupleLayerLinks LG hQ) hspan hg' R a b
    (coupleInternalLinkDomain LG hQ) (measurableSet_coupleInternalLinkDomain hQ)
    (coupleInternalLinkDomain_subset_boxes d hQ) (coupleInputFunctionsL LG H)
    (fun a => coupleInputFunctions_spatialNorm_leL hQ H hH a)
    (timeBox q q') (fun t ht => (hshift t ht).1) (fun t ht => (hshift t ht).2) hχrect
    (gardenCircle LG.garden) univ G
  rw [hcount] at hraw
  have heq : (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
      coupleLeavesStar L γ δ LG S ω H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => weightedSourceOneClockKernel (coupleCarrier hQ) (G.at k.1) (gardenCircle LG.garden) R a
        L γ δ (coupleLayerLinks LG hQ) (coupleInternalLinkDomain LG hQ)
        (coupleInputFunctionsL LG H) ts.1 k.1 := by
    funext ts k
    exact coupleLeavesW_eq_weightedOneClock_of_summable hQ hn a hroot hwidth L γ δ H k.1 ts.1
      (starWeight S ω) (G.at k.1) (couple_starWeight_eq_value hQ (30 * d) S ω c hω L k.1)
      (couple_lattice_summable hQ (by omega) L hLone H hB hH k.1)
  rw [heq]
  refine hraw.trans ?_
  gcongr
  exact starRootMeasure_momentMass_le (30 * d) S ω c hω (coupleRow hQ)

end WaveTurbulence.Flower.IncTop