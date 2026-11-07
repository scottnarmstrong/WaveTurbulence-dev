/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD14
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN10
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: the vine case at the representative (B4)

`CvineF`: the explicit large constant of the vine case (depends only on `d`, `η` and the gate constant).
`vineCaseRepresents_of_gate`: `VineCaseRepresents {Pg with C₁ := C}` from the two leafwise gates (through `GateEnv Pg`),
V5's `VineEstCanonLayerHalfMK` at the parameter record, and `VINEPARAM` (M9).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
open scoped ENNReal Classical

/-- The explicit minimal constant of the vine case. -/
noncomputable def CvineF (d : ℕ) (η c₁ : ℝ) : ℝ :=
  max (max (max 1 (2 * c₁ ^ 2 * (1 + cLeib d (30 * d)))) (Cchi d * (nodeBallCard d : ℝ) * Kslot d η ^ 2))
    (Cchi d * (nodeBallCard d : ℝ) * (9 * KslotM d η) ^ 2 * max 1 (ChinF d η))

theorem eta_small_facts (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    6 * η ^ 6 ≤ η ∧ 6 * η ^ 6 ≤ 1 ∧ 2 * (6 * η ^ 6) ≤ η := by
  have h5 : η ^ 5 ≤ (1 / 2 : ℝ) ^ 5 := pow_le_pow_left₀ hη.le hη2 5
  have h6 : 6 * η ^ 6 = 6 * η ^ 5 * η := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [h6]; nlinarith
  · have : η ^ 6 ≤ η ^ 5 := pow_le_pow_of_le_one hη.le (by linarith) (by norm_num)
    nlinarith
  · rw [h6]; nlinarith


theorem gsk_of_spec {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (σ : Prescription S) :
    gskOf (gregOf D hS LG) S σ (RegRed.coreLayer LG D hS hd) =
      gskOf (gregOf D hS (layeredReconstruction D hS layer hLayer)) S σ (fun v => layer (D.coreBranch hS v).toNode) := by
  subst hspec
  rfl

theorem nor_card_eq {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) :
    (Finset.univ.filter fun i : Fin n => (assemblyShape hM9 B).nor i = false).card =
      (Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card := by
  simp only [assemblyShape, shapeFamily]
  congr 1
  ext i
  simp
  exact fun _ => Finset.mem_univ _

theorem normalizedPiece_bsk {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).bsk = bskOf a.prime.skeleton a.totalSigma := rfl

/-- The parameter record with the large constant `C₁` replaced. -/
abbrev PB (Pg : WTParams) (C : ℝ) : WTParams := {Pg with C₁ := C}

section VineCase
variable (Pg : WTParams) (C : ℝ)

theorem vineCaseRepresents_of_gate (E : GateEnv Pg) (hη : 0 < Pg.η) (hδ : 0 < Pg.δ)
    (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM) (hC : CvineF Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : VineEstCanonLayerHalfMK (PB Pg C)) :
    VineCaseRepresents (PB Pg C) := by
  intro p hp R hR hRmax N hN1 hNmax A hA hcl tt htt base roots U s hs0 hb hsize π hv
  obtain ⟨K, hK1, hKe, hslot⟩ := vine_slot_data Pg E
  have hcLeib := cLeib_nonneg Pg.d (30 * Pg.d)
  have hC1' : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hC)
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * K) ^ 2 * max 1 (ChinF Pg.d Pg.η) ≤ C := by
    rw [hKe]; exact le_trans (le_max_right _ _) hC
  have hC1ge : 1 ≤ C := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hC
  obtain ⟨hη6, hη1, hη12⟩ := eta_small_facts Pg.η hη E.hη
  have hCg : Pg.C₁ ≤ C := by nlinarith [E.hC1]
  have hgate : CoherentGateH (PB Pg C) :=
    coherentGateH_of (leafwiseCoherentApproximation30_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hcoh)
  have hinc : IncoherentGateH (PB Pg C) :=
    incoherentGateH_of (leafwiseIncoherentDecay_largeConstantMonotone Pg C Pg.C₂ E.hC1 hC2 hδ hL2 hCg le_rfl E.hinc)
  have hd1 : 1 ≤ Pg.d := E.hd1
  have hL1 : 1 ≤ Pg.L := E.hL1
  have hL0 : Pg.L ≠ 0 := (lt_of_lt_of_le zero_lt_one hL1).ne'
  obtain ⟨a, ha⟩ : ∃ a, repPt π = a := ⟨_, rfl⟩
  have haA : a.layered ∈ A := ha ▸ repPt_layered_mem π
  have hcA := hA a.layered haA
  have hcan : IsCanonGC (p + 1) a.layered := hcA.1
  have hdec := a.prime.data.decoded_order a.prime.prime.1 a.prime.decodes
  have hNmax' : N ≤ Pg.N (p + 1) ^ 4 := by rw [N_bumpC1] at hNmax; exact hNmax
  have hordN : a.layered.garden.order = N := hcA.2.2.1
  have hsz : a.prime.data.size ≤ Pg.N (p + 1) ^ 4 := by omega
  have hGplain : a.fullProfile.piece.gap.garden.IsPlain :=
    (stSt a.prime.skeleton a.totalSigma).plain a.prime.prime.1
  have hctrlA : ∀ LG ∈ A, U.toLF.Controlled LG := controlled_of_bounded hA U hb
  have hctrl_a : ∀ i, LeafwiseControlled a.layered (typeProfiles a.layered (U.h i)) (fun _ => U.b i) :=
    fun i => hctrlA _ haA i
  obtain ⟨fam, μ, hexpR, hμ, hμb⟩ := hslot C hC1' a hp hcan hsz tt htt U hctrl_a hGplain
  obtain ⟨T, hT⟩ := exists_outputs_finset (p := p) a
  have hlay := fun y hy x => member_stateLayer_le hA hcl a haA y hy x
  have hctrlM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered :=
    fun y hy => hctrlA _ (outputs_mem_A hcl a haA hcan y hy)
  have hsum := class_sum_modes π a ha (PB Pg C) U hd1 hL1 tt htt base roots hlay hb hctrlM
    hGplain fam hexpR T hT
  have hcanR : IsCanonGC (p + 1) (repPt π).layered := by rw [ha]; exact hcan
  have hTR : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) := by
    rw [ha]; exact hT
  rw [sum_members_eq hcl π hcanR _ U.toLF tt base roots T hTR, hsum]
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  letI : Fintype U.ι := U.fin
  have hsgn : ∀ i : U.ι, ‖((U.sign i : ℝ) : ℂ)‖ ≤ 1 := fun i => by
    rw [Complex.norm_real]; exact U.sign_abs_le i
  have key : Stage1Piece.RepresentsIntA (P := (PB Pg C)) (a.normalizedPiece (PB Pg C).d) N tt base roots s
      (∑ i : U.ι, ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden (PB Pg C).L (PB Pg C).γ (PB Pg C).δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z
              then 1 else 0) hGplain
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hGplain)
            ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
            (fun j lam t k => unitHk (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a)
              (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)) := by
    refine representsIntA_of_vineModes (P := (PB Pg C)) hd1 hL1 E.hη0 (a.normalizedPiece (PB Pg C).d) hGplain tt base roots
      (selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots) ?_
      ((profileShape a).route a.prime.prime.1 hGplain)
      (fun s i => (profileShape a).route_natural a.prime.prime.1 hGplain s i)
      ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma)) ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
      (stSrc hMa a.totalSigma hGplain) (fun j i x hx z => stSrc_dart hMa a.totalSigma hGplain j i x hx roots z)
      (fun j i r hr z => stSrc_root hMa a.totalSigma hGplain j i r hr roots z)
      (fun i : U.ι => ((U.sign i : ℝ) : ℂ)) hsgn fam μ
      (fun i j lam t k => unitHk (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)
      (c := 6 * (PB Pg C).η ^ 6) (θ := (PB Pg C).η) (by positivity) hη1 hη12 hμ
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) K (max 1 (ChinF Pg.d Pg.η)) rfl hK1 (le_max_left _ _) hCχ
      (fun s' => slotSize a.prime.data ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun s' => slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun i s' => slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
        ((profileShape a).iota a.prime.prime.1 hGplain s'))
      ?_ hμb
      (fun i j => unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) (U.b i))
      (fun j => clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)))
      (fun j => cohmolIndex (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) +
        (step3D hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (canonBadKind hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a))
          (qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlk hMa a.totalSigma j).upper
            (unitBlk hMa a.totalSigma j).lower (regionOf (unitBlk hMa a.totalSigma j)))
          (fun _ => (0 : Mom (PB Pg C).d)) (0 : Mom (PB Pg C).d)).M₁)
      (fun j => (Finset.univ.filter fun i : Fin (unitN a.totalSigma j) =>
        (assemblyShape hM9 (sourceAssembly a j)).nor i = false).card)
      (fun i j => regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
        (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)))
      ?_ ?_ ?_ N s ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
    · intro D' hD z
      exact (PrescribedPrimeGarden.normalizedPiece_gapIndicator a D' hD (lt_of_lt_of_le zero_lt_one hL1).ne' _ _ base roots z).trans
        (selSkC_ite a _ _ _ (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z)
    · intro i s'
      generalize (profileShape a).iota a.prime.prime.1 hGplain s' = s0
      unfold slotLeaf
      rcases s0 with p' | b
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    · intro i j
      exact WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)
    · intro i j
      have hb0 : 0 ≤ ((U.b i : NNReal) : ℝ) := NNReal.coe_nonneg _
      refine ⟨?_, le_of_eq ?_⟩
      · unfold unitMass
        have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
          mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
        exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
          (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ hb0)
      · unfold unitMass
        rw [nor_card_eq hM9 (sourceAssembly a j)]
        simp only [neg_mul]
    · intro i ξ
      have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
      have hordg : (a.prime.data.garden a.prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
        rw [a.prime.gardenEq, hordN]; exact hNmax
      obtain ⟨H, Mh, hsum, hHk, hprod⟩ := unit_hinge_data (PB Pg C) hV hM9 hgate hinc hd1 hη hη6 E.hη hC1ge hδ hL1 hw hp a
        hcan hordg tt base roots (U.h i) (U.b i) (NNReal.coe_nonneg _) (fun q j j' hq => hb i q j j' hq)
        (modLam (fun s => (fam i).m s (ξ s)) ((profileShape a).route a.prime.prime.1 hGplain))
      refine ⟨H, Mh, hsum, hHk, ?_⟩
      rw [hprod]
      have hM0 : ∀ j, 0 ≤ unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) (U.b i) := fun j => by
        unfold unitMass
        have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
          mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
        exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
          (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
      have hpr : 0 ≤ ∏ j, unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) (U.b i) := Finset.prod_nonneg fun j _ => hM0 j
      have hlam : 0 ≤ ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s))
          ((profileShape a).route a.prime.prime.1 hGplain) j : ℤ) : ℝ)|) ^ (6 * (PB Pg C).η ^ 6) :=
        Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
      have hch := ChinF_spec Pg.d Pg.η E.hη0
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hpr) hlam
      exact pow_le_pow_left₀ hch (le_max_right _ _) _
    · have hprodeq : ∀ i : U.ι, (∏ t, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (fun _ => U.b i) ((profileShape a).iota a.prime.prime.1 hGplain t)) *
          ∏ j, regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
            (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)) =
          leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [leaf_prod_split (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
          (sourceLayer a) (sourceLayer_isLayering a) (U.b i), sourceLayer_reconstructs a]
      calc _ ≤ ∑ i : U.ι, leafSizeProduct a.layered (fun _ => U.b i) := Finset.sum_le_sum fun i _ => by
            have hnn : 0 ≤ leafSizeProduct a.layered (fun _ => U.b i) :=
              Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
            exact (mul_le_of_le_one_left (hnn.trans (hprodeq i).symm.le) (hsgn i)).trans (hprodeq i).le
        _ = U.toLF.size a.layered := rfl
        _ ≤ s := hsize a.layered haA
    · have hn : N - a.prime.skeleton.order = a.prime.data.size := by omega
      exact exponent_order (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain N hn
        (by omega)
    · have h1 := gsk_bound (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
        (sourceLayer a) (sourceLayer_isLayering a) a.totalSigma (B₀ := sourceAssembly a)
        (hcov_units hMa a.totalSigma)
        (fun v => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 v).toNode) (fun v => rfl)
      have h2 := gsk_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
        (sourceLayer_reconstructs a) a.prime.decodes a.totalSigma
      refine le_trans (le_of_eq h2) (le_trans h1 (le_of_eq ?_))
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [step3D_M1]
      rfl
    · refine le_trans (le_of_eq (normalizedPiece_bsk a _))
        (bsk_bound hM9 a.totalSigma (sourceAssembly a) (hcov_units hMa a.totalSigma))
    · exact le_of_eq ((card_hinges (profileShape a) (unitBlk_disj hMa a.totalSigma)).symm.trans
        (congrArg Finset.card (profileShape_hinges a)))
    · exact card_units_le_order (profileShape a) (unitBlk_disj hMa a.totalSigma)
    · rfl
  subst ha
  exact key

end VineCase

end WaveTurbulence.Represents
