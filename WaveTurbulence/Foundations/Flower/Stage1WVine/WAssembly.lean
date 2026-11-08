/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WCount
public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge

/-! # STAGE1W-VINE (T6, part 5): the weighted vine case at one parameter record

`vineCaseRepresentsFW_of_gate` (main's `vineCaseRepresents_of_gate`, RepVD15, with the frontier weight):
`VineCaseRepresentsFW {Pg with C₁ := C}` from the two leafwise gates (through `GateEnv Pg`), INC-TOP's
`TopIncoherentDecayAtR` (at `Pg` for the outer slots, at `{Pg with C₁ := C}` for T5), and the staged
**`V5FrontierClassBoundAt {Pg with C₁ := C}`**.

Weight bookkeeping: the outer slot `s'` carries `cψ ^ slotNr`, unit `j` carries `cψ ^ (9 |U_j| + 4 n₂(j))` and the
fixed constant `topFilterMass` (absorbed into the hinge constant `ChFW d η`); both `cψ`-powers are folded into the leaf
factors `lf`, `lfj` of main's `representsIntA_of_vineModes`, and their total exponent is `≤ 16 N` (`weight_exponent_le`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W
open scoped ENNReal Classical

/-- The hinge constant of the weighted units, with the top filter mass absorbed. -/
def ChFW (d : ℕ) (η : ℝ) : ℝ := max 1 (ChinFW d η * topFilterMass)

/-- The explicit minimal constant of the weighted vine case. -/
def CvineFW (d : ℕ) (η c₁ : ℝ) : ℝ :=
  max (max 1 (2 * c₁ ^ 2 * (1 + cLeib d (30 * d))))
    (Cchi d * (nodeBallCard d : ℝ) * (9 * KslotMW d η) ^ 2 * ChFW d η)

/-- The VINEEST mass of a unit with its weight power (without the top filter mass). -/
def unitMassC (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (cψ B₀ : ℝ) : ℝ :=
  cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * unitMass P hM9 B RD hG layer hLayer B₀

theorem prod_pow_mul_prod {ι : Type*} [Fintype ι] (c : ℝ) (e : ι → ℕ) (f : ι → ℝ) :
    ∏ i, (c ^ e i * f i) = c ^ (∑ i, e i) * ∏ i, f i := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

section VineCase
variable (Pg : WTParams) (C : ℝ)

theorem vineCaseRepresentsFW_of_gate (E : GateEnv Pg) (htop0 : TopIncoherentDecayAtR Pg) (hη : 0 < Pg.η)
    (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM) (hC : CvineFW Pg.d Pg.η Pg.C₁ ≤ C)
    (hV : V5FrontierClassBoundAt (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C)) :
    VineCaseRepresentsFW (PB Pg C) := by
  intro p hp R hR hRmax N hN1 hNmax A hA hcl tt htt base roots g cψ hcψ hgp hre U s hs0 hb hsize π hv
  obtain ⟨K, hK1, hKe, hslot⟩ := vine_slot_dataW Pg E htop0
  have hcLeib := cLeib_nonneg Pg.d (30 * Pg.d)
  have hC1' : 2 * Pg.C₁ ^ 2 * (1 + cLeib Pg.d (30 * Pg.d)) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCχ : Cchi Pg.d * (nodeBallCard Pg.d : ℝ) * (9 * K) ^ 2 * ChFW Pg.d Pg.η ≤ C := by
    rw [hKe]; exact le_trans (le_max_right _ _) hC
  have hC1ge : 1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
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
  have hc0 : 0 ≤ cψ := by linarith
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
  obtain ⟨fam, μ, hexpR, hμ, hμb⟩ := hslot C hC1' a hp hcan hsz tt htt U hctrl_a g cψ hcψ hgp hGplain
  obtain ⟨T, hT⟩ := exists_outputs_finset (p := p) a
  have hlay := fun y hy x => member_stateLayer_le hA hcl a haA y hy x
  have hcanM := fun y hy => member_isCanon hA hcl a haA y hy
  have hctrlM : ∀ y : UState (2 * R) (unitsSplit (sourceAssembly a)),
      y ∈ sourceClass a p (objKind (2 * R)) → U.toLF.Controlled y.1.layered :=
    fun y hy => hctrlA _ (outputs_mem_A hcl a haA hcan y hy)
  have hgn : ∀ j x, ‖g j x‖ ≤ cψ := fun j x => (hgp j).norm_le hc0 x
  have hsum := class_sum_modesW π a ha (PB Pg C) U hd1 hL1 tt htt base roots hlay hcanM hb hctrlM g cψ hcψ hgn
    hGplain fam hexpR T hT
  have hcanR : IsCanonGC (p + 1) (repPt π).layered := by rw [ha]; exact hcan
  have hTR : (T : Set (LayeredGarden (2 * R))) = (repPt π).outputs (p := p) (kind := objKind (2 * R)) := by
    rw [ha]; exact hT
  rw [sum_members_eqW hcl π hcanR _ U.toLF tt base roots (fwWeight p g base) T hTR, hsum]
  have hMa := Mole.garden_isMolecule a.prime.skeleton
  letI : Fintype U.ι := U.fin
  have hsgn : ∀ i : U.ι, ‖((U.sign i : ℝ) : ℂ)‖ ≤ 1 := fun i => by
    rw [Complex.norm_real]; exact U.sign_abs_le i
  have hn : N - a.prime.skeleton.order = a.prime.data.size := by omega
  have hnS : a.prime.skeleton.order ≤ N := by omega
  have hordD : (a.prime.data.garden a.prime.prime.1).order = N := by rw [a.prime.gardenEq, hordN]
  have hexpo := weight_exponent_le (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1
    hGplain N hn hnS
  have hE : (∑ s', Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 ((profileShape a).iota a.prime.prime.1 hGplain s')) +
      ∑ j, (9 * (unitBlk hMa a.totalSigma j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) ≤ 16 * N := by
    rw [hordD] at hexpo; omega
  have hmc : ∀ (i : U.ι) j, unitMassC (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) =
      cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
        4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
      unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) (U.b i) := fun i j => rfl
  have hM0 : ∀ (i : U.ι) j, 0 ≤ unitMass (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) (U.b i) := fun i j => by
    unfold unitMass
    have hx0 : 0 ≤ (PB Pg C).C₁ * Real.sqrt (PB Pg C).δ :=
      mul_nonneg (by have : (1 : ℝ) ≤ C := hC1ge; show 0 ≤ C; linarith) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0 _) (Real.rpow_nonneg (by
      have : (1 : ℝ) ≤ Pg.L := hL1; show 0 ≤ Pg.L; linarith) _))
      (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
  have hMC0 : ∀ (i : U.ι) j, 0 ≤ unitMassC (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) := fun i j => by
    rw [hmc]; exact mul_nonneg (pow_nonneg hc0 _) (hM0 i j)
  have key : Stage1Piece.RepresentsIntA (P := (PB Pg C)) (a.normalizedPiece (PB Pg C).d) N tt base roots
      (cψ ^ (16 * N) * s)
      (∑ i : U.ι, ((U.sign i : ℝ) : ℂ) * ∑' ξ : (∀ s, (fam i).Λ s), ((modeWt (fam i) ξ : ℝ) : ℂ) *
          outerValM a.fullProfile.piece.gap.garden (PB Pg C).L (PB Pg C).γ (PB Pg C).δ base roots tt
            a.fullProfile.piece.layer a.fullProfile.piece.hinges
            (fun z => if selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z
              then 1 else 0) hGplain
            (fun s' => (fam i).a s' (ξ s')) (fun s' => (fam i).m s' (ξ s'))
            ((profileShape a).route a.prime.prime.1 hGplain)
            ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma))
            ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
            (fun j lam t k => unitHkFW (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
              (sourceLayer_isLayering a) g
              (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)) := by
    refine representsIntA_of_vineModes (P := (PB Pg C)) hd1 hL1 E.hη0 (a.normalizedPiece (PB Pg C).d) hGplain tt base
      roots (selSkC a (PB Pg C).L (PB Pg C).γ (PB Pg C).η (lt_of_lt_of_le zero_lt_one hL1).ne' base roots) ?_
      ((profileShape a).route a.prime.prime.1 hGplain)
      (fun s i => (profileShape a).route_natural a.prime.prime.1 hGplain s i)
      ((profileShape a).hclk (unitBlk_disj hMa a.totalSigma)) ((profileShape a).hmom (unitBlk_disj hMa a.totalSigma))
      (stSrc hMa a.totalSigma hGplain) (fun j i x hx z => stSrc_dart hMa a.totalSigma hGplain j i x hx roots z)
      (fun j i r hr z => stSrc_root hMa a.totalSigma hGplain j i r hr roots z)
      (fun i : U.ι => ((U.sign i : ℝ) : ℂ)) hsgn fam μ
      (fun i j lam t k => unitHkFW (PB Pg C) p (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) g (unitProfile (unitBlk hMa a.totalSigma) (U.h i) j) base lam t k)
      (c := 6 * (PB Pg C).η ^ 6) (θ := (PB Pg C).η) (by positivity) hη1 hη12 hμ
      ((PB Pg C).C₁ * Real.sqrt (PB Pg C).δ) K (ChFW Pg.d Pg.η) rfl hK1 (le_max_left _ _) hCχ
      (fun s' => slotSize a.prime.data ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun s' => slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
        ((profileShape a).iota a.prime.prime.1 hGplain s'))
      (fun i s' => cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
          ((profileShape a).iota a.prime.prime.1 hGplain s') *
        slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
          ((profileShape a).iota a.prime.prime.1 hGplain s'))
      ?_ hμb
      (fun i j => unitMassC (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) cψ (U.b i))
      (fun j => clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)))
      (fun j => cohmolIndex (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) +
        (step3D hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (canonBadKind hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a))
          (qOutOf a.prime.data a.prime.prime.1 (sourceLayer a) (unitBlk hMa a.totalSigma j).upper
            (unitBlk hMa a.totalSigma j).lower (regionOf (unitBlk hMa a.totalSigma j)))
          (fun _ => (0 : Mom (PB Pg C).d)) (0 : Mom (PB Pg C).d)).M₁)
      (fun j => (Finset.univ.filter fun i : Fin (unitN a.totalSigma j) =>
        (assemblyShape hM9 (sourceAssembly a j)).nor i = false).card)
      (fun i j => cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
          4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
        regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
          (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)))
      ?_ ?_ ?_ N (cψ ^ (16 * N) * s) ?_ ?_ ?_ ?_ ?_ ?_ _ ?_
    · intro D' hD z
      exact (PrescribedPrimeGarden.normalizedPiece_gapIndicator a D' hD (lt_of_lt_of_le zero_lt_one hL1).ne' _ _ base
        roots z).trans (selSkC_ite a _ _ _ (lt_of_lt_of_le zero_lt_one hL1).ne' base roots z)
    · intro i s'
      refine mul_nonneg (pow_nonneg hc0 _) ?_
      generalize (profileShape a).iota a.prime.prime.1 hGplain s' = s0
      unfold slotLeaf
      rcases s0 with p' | b
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
      · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
    · intro i j
      exact mul_nonneg (pow_nonneg hc0 _)
        (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _))
    · intro i j
      refine ⟨hMC0 i j, le_of_eq ?_⟩
      rw [hmc]
      unfold unitMass
      rw [nor_card_eq hM9 (sourceAssembly a j)]
      simp only [neg_mul]
      ring
    · intro i ξ
      have hw : 0 ≤ Pg.gamma1 - Real.sqrt Pg.η := le_trans (pow_nonneg E.hη0 8) E.hκ
      have hordg : (a.prime.data.garden a.prime.prime.1).order ≤ (PB Pg C).N (p + 1) ^ 4 := by
        rw [a.prime.gardenEq, hordN]; exact hNmax
      obtain ⟨H, Mh, hsum', hHk, hprod⟩ := unit_hinge_dataW (PB Pg C) hV hM9 hgate hinc htop hd1 hη hη6 E.hη hC1ge
        hδ hL1 hw hp a hcan hordg tt base roots g cψ hcψ hgp hre (U.h i) (U.b i) (NNReal.coe_nonneg _)
        (fun q j j' hq => hb i q j j' hq)
        (modLam (fun s => (fam i).m s (ξ s)) ((profileShape a).route a.prime.prime.1 hGplain))
      refine ⟨H, Mh, hsum', hHk, ?_⟩
      have hpt : ∀ j, ChinFW (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
          a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) ≤
          ChFW Pg.d Pg.η * unitMassC (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
            (sourceLayer_isLayering a) cψ (U.b i) := fun j => by
        have e : ChinFW (PB Pg C).d (PB Pg C).η * unitMassFW (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
            a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) =
            (ChinFW Pg.d Pg.η * topFilterMass) * unitMassC (PB Pg C) hM9 (sourceAssembly a j) a.prime.data
              a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) cψ (U.b i) := by
          unfold unitMassFW unitMassC
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hMC0 i j)
      have hlam : 0 ≤ ∏ j, (1 + |((modLam (fun s => (fam i).m s (ξ s))
          ((profileShape a).route a.prime.prime.1 hGplain) j : ℤ) : ℝ)|) ^ (6 * (PB Pg C).η ^ 6) :=
        Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
      have hch := ChinFW_spec Pg.d Pg.η E.hη0
      rw [hprod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun j _ => mul_nonneg hch
        (unitMassFW_nonneg (PB Pg C) hM9 (sourceAssembly a j) a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) cψ (U.b i) hc0 (by show (0 : ℝ) ≤ C; linarith) hL0 (NNReal.coe_nonneg _)))
        (fun j _ => hpt j)) hlam
    · have hprodeq : ∀ i : U.ι, (∏ t, slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (fun _ => U.b i) ((profileShape a).iota a.prime.prime.1 hGplain t)) *
          ∏ j, regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
            (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ)) =
          leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [leaf_prod_split (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain
          (sourceLayer a) (sourceLayer_isLayering a) (U.b i), sourceLayer_reconstructs a]
      have hfac : ∀ i : U.ι, (∏ t, (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
            ((profileShape a).iota a.prime.prime.1 hGplain t) *
          slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
            ((profileShape a).iota a.prime.prime.1 hGplain t))) *
          ∏ j, (cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
            4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
            regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j)) (sourceLayer a)
              (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ))) ≤
          cψ ^ (16 * N) * leafSizeProduct a.layered (fun _ => U.b i) := fun i => by
        rw [prod_pow_mul_prod, prod_pow_mul_prod, mul_mul_mul_comm, ← pow_add, hprodeq i]
        have hnn : 0 ≤ leafSizeProduct a.layered (fun _ => U.b i) :=
          Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ hE) hnn
      calc _ ≤ ∑ i : U.ι, cψ ^ (16 * N) * leafSizeProduct a.layered (fun _ => U.b i) :=
            Finset.sum_le_sum fun i _ => by
              have hnn : 0 ≤ (∏ t, (cψ ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1
                    ((profileShape a).iota a.prime.prime.1 hGplain t) *
                  slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (fun _ => U.b i)
                    ((profileShape a).iota a.prime.prime.1 hGplain t))) *
                  ∏ j, (cψ ^ (9 * (unitBlk hMa a.totalSigma j).atoms.card +
                    4 * clLocalOrder2 a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))) *
                    regionLeafSize a.prime.data a.prime.prime.1 (regionOf (unitBlk hMa a.totalSigma j))
                      (sourceLayer a) (sourceLayer_isLayering a) (fun _ => ((U.b i : NNReal) : ℝ))) := by
                refine mul_nonneg (Finset.prod_nonneg fun t _ => mul_nonneg (pow_nonneg hc0 _) ?_)
                  (Finset.prod_nonneg fun j _ => mul_nonneg (pow_nonneg hc0 _)
                    (WaveTurbulence.VineEstS5C.regionLeafSize_const_nonneg _ _ _ _ _ (NNReal.coe_nonneg _)))
                generalize (profileShape a).iota a.prime.prime.1 hGplain t = s0
                unfold slotLeaf
                rcases s0 with p' | b
                · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
                · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
              exact (mul_le_of_le_one_left hnn (hsgn i)).trans (hfac i)
        _ = cψ ^ (16 * N) * U.toLF.size a.layered := by rw [← Finset.mul_sum]; rfl
        _ ≤ cψ ^ (16 * N) * s := mul_le_mul_of_nonneg_left (hsize a.layered haA) (pow_nonneg hc0 _)
    · exact exponent_order (profileShape a) (unitBlk_disj hMa a.totalSigma) a.prime.data a.prime.prime.1 hGplain N hn
        hnS
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

end WaveTurbulence.Flower.Stage1WVine
