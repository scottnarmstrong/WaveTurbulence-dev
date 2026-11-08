/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WB.Statement
public import WaveTurbulence.Foundations.Flower.V5WB.B.Export
public import WaveTurbulence.Foundations.Flower.V5WB.B.Bridge
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatPrefix
public import WaveTurbulence.Foundations.Flower.V5WB.K.WeightedTrunc
public import WaveTurbulence.Foundations.Flower.IncTop.Gate
public import WaveTurbulence.Foundations.LemLin.ScalarPeriod

/-! # V5W-B-WORLD B5: the weighted vine class bound at `S = none`

* `enginePullback_bWN`: the masked, normalized bond weight of a block has an engine pullback of mass
  `cψ ^ (3|U|) · ∏ nodeNorm` (top darts of coherent rows: the presentation of `g`; incoherent rows: the constants).
* `rowNorm_le`: the row normalization of a region is at most `cψ ^ (2 n₂ + 2 n₁)`.
* `one_le_topFilterMass`: `∫ ‖𝓕 χ₀‖ ≥ |χ₀(0)| = 1` (Fourier inversion).
* `v5FrontierClassBoundNoneAt_of_flat`: at a record where the weighted flat estimate holds for every selector, the pinned
  class kernel at `S = none` is the selector class at `selW p (g a) cψ` with the masked weight
  (`twistedRecenteredFW_none_eq`), which is the weighted flat observable of the representative
  (`twistedRecenteredModCX_bond_eq_flatFn`, the class identity carried through FLAT-MOD with the masked weight), whose
  multiplier has an engine pullback of mass `cψ^{3|U|}·rowNorm ≤ cψ^{9|U| + 4 n₂} · topFilterMass`.
* **`v5FrontierClassBoundNone : WTPrefix (V5FrontierClassBoundOnAt (· = none))`**, from main's certificate for every
  selector (`uniformTermCertKS`), main's two leafwise gates, `RealityAll` and INC-TOP's gate.
* `v5FrontierClassBound_of_top`: the gate `V5FrontierClassBound` from the `S ≠ none` half (V5W-T).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WB
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback enginePullback_one)
open WaveTurbulence.VineSpaceB (regionDarts mem_regionDarts layX enginePullback_mono enginePullback_congr
  enginePullback_finsetProd enginePullback_nodeValue topDarts card_topDarts_le)
open WaveTurbulence.Flower.V5W (nodeRowIncoh twistedRecenteredFW topFilterMass V5FrontierClassBound
  V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal FourierTransform
open VineEstS5C.P4.Final LGSpine

/-! ## The engine pullback of the masked, normalized weight -/

theorem const_presented {d : ℕ} (r : ℝ) :
    ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ |r| ∧ ∀ x, M.value x = r := by
  refine ⟨Unit, inferInstance,
    { μ := Measure.dirac ()
      sigmaFinite := inferInstance
      frequency := fun _ => 0
      frequency_measurable := measurable_const
      amplitude := fun _ => (r : ℂ)
      amplitude_integrable := integrable_const _ }, ?_, ?_⟩
  · simp [Cut2A.SpatialMeasure.mass]
  · intro x
    simp [Cut2A.SpatialMeasure.value]

section Pull
variable {w d : ℕ} {ι : Type*} {U : Finset (GBranch _)} 

/-- **The engine pullback of the masked, normalized bond weight of a block.** -/
theorem enginePullback_bWN (X : FamilyReconstruction w ι) {U : Finset (GBranch X.skeleton.tree)}
    {a b : GBranch X.skeleton.tree} (R : CLRegionData X.skeleton U a b) (hU : X.skeleton.molecule.IsBlock U a b)
    (L : ℝ) (base : Mom d) (p : ℕ) (g : Mom d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ)
    (hpres : ∃ (α : Type) (_ : MeasurableSpace α) (M : Cut2A.SpatialMeasure (Mom d) α),
      M.mass ≤ cψ ∧ ∀ x, M.value x = g x) :
    EnginePullback R L base (bondWD X.skeleton (ΨX (wdOf p g cψ) X) L base (layX X) U)
      (cψ ^ (3 * U.card) * ∏ y ∈ regionDarts X.skeleton U,
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
  classical
  have hc0 : 0 ≤ cψ := by linarith
  let T : GardenDart X.skeleton → Prop := fun y =>
    layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)) < p ∧ layX X (X.skeleton.molecule.atom y) = p
  have hfac : ∀ y ∈ regionDarts X.skeleton U, EnginePullback R L base
      (fun z => ΨX (wdOf p g cψ) X y (layX X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
        (layX X (X.skeleton.molecule.atom y)) (cosetDecoration X.skeleton L base z (Mole.dartNode X.skeleton y)))
      ((if T y then cψ else 1) *
        nodeNorm X.data X.plain (stateLayer X) (stateLayer_isLayering X) cψ (Mole.dartNode X.skeleton y)) := by
    intro y _
    unfold ΨX nodeNorm
    by_cases hi : nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0
    · simp only [hi, ↓reduceIte, mul_one, wdOf]
      by_cases hy : T y
      · rw [if_pos hy]
        obtain ⟨α, _, M, hM, hv⟩ := hpres
        refine enginePullback_mono R L base (enginePullback_congr R L base
          (enginePullback_nodeValue R L base M (Mole.dartNode X.skeleton y)) ?_) hM
        funext z
        rw [hv]
        exact (if_pos hy).symm
      · rw [if_neg hy]
        refine enginePullback_congr R L base (enginePullback_one R L base) ?_
        funext z
        simp only [topPsi]
        rw [if_neg hy]
    · simp only [hi, ↓reduceIte]
      obtain ⟨α, _, M, hM, hv⟩ := const_presented (d := d)
        (cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2))
      have hr : 0 ≤ cψ ^ ((nodeRowExp X.data X.plain (stateLayer X) (stateLayer_isLayering X)
          (Mole.dartNode X.skeleton y) : ℝ) / 2) := Real.rpow_nonneg hc0 _
      have h1 : (1 : ℝ) ≤ if T y then cψ else 1 := by split_ifs <;> linarith
      refine enginePullback_mono R L base (enginePullback_congr R L base
        (enginePullback_nodeValue R L base M (Mole.dartNode X.skeleton y)) ?_) ?_
      · funext z
        rw [hv]
        rfl
      · rw [abs_of_nonneg hr] at hM
        exact hM.trans (le_mul_of_one_le_left hr h1)
  have hprod := enginePullback_finsetProd R L base (regionDarts X.skeleton U) _ _ hfac
  rw [Finset.prod_mul_distrib] at hprod
  have hmass : (∏ y ∈ regionDarts X.skeleton U, if T y then cψ else 1) =
      cψ ^ (topDarts X.skeleton (layX X) U p).card := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  rw [hmass] at hprod
  refine enginePullback_mono R L base hprod ?_
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hcψ ?_)
    (Finset.prod_nonneg fun y _ => ?_)
  · have := card_topDarts_le hU (layX X) p
    omega
  · unfold nodeNorm
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_nonneg hc0 _

end Pull

/-! ## The mass -/

/-- **The row normalization of a region is at most `cψ ^ (2 n₂ + 2 n₁)`.** -/
theorem rowNorm_le {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {cψ : ℝ} (hc : 1 ≤ cψ) (D : ReconstructionData G) (hG : G.IsPlain) (hB : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) :
    rowNorm cψ D hG R layer hLayer ≤ cψ ^ (2 * clLocalOrder2 D hG R + 2 * clLocalOrder1 R) := by
  have hc0 : 0 ≤ cψ := by linarith
  unfold rowNorm
  have h1 : ∏ pr ∈ clRegionalPairs hG U, coupleNorm cψ D hG layer hLayer pr ≤
      ∏ pr ∈ clRegionalPairs hG U, cψ ^ (2 * (nativeCoupleLayered D hG layer hLayer pr).garden.order + 2) := by
    apply Finset.prod_le_prod₀
    · intro pr _; unfold coupleNorm; split_ifs <;> positivity
    · intro pr _; unfold coupleNorm; split_ifs
      · exact one_le_pow₀ hc
      · exact le_rfl
  have h2 : ∏ v ∈ clInteriorBranches R, treeNorm cψ D hG layer hLayer v ≤
      ∏ v ∈ clInteriorBranches R, cψ ^ (2 * (nativeChainLayered D hG layer hLayer v).garden.order + 2) := by
    apply Finset.prod_le_prod₀
    · intro v _; unfold treeNorm; split_ifs <;> positivity
    · intro v _; unfold treeNorm; split_ifs
      · exact one_le_pow₀ hc
      · exact pow_le_pow_right₀ hc (by omega)
  refine (mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => by unfold treeNorm; split_ifs <;> positivity)
    (Finset.prod_nonneg fun _ _ => by positivity)).trans (le_of_eq ?_)
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add]
  congr 1
  have e2 := clLocalOrder2_eq_native_orders D hG R layer hLayer
  have e1 := card_clRegionalPairs hB R hG
  have e3 : (clInteriorBranches R).card = clLocalOrder1 R := rfl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.sum_const, e1, e3, e2]
  simp only [smul_eq_mul]
  ring

/-- **`topFilterMass ≥ 1`**: `1 = χ₀(0) = 𝓕⁻(𝓕 χ₀)(0)`, of norm at most `∫ ‖𝓕 χ₀‖`. -/
theorem one_le_topFilterMass : 1 ≤ topFilterMass := by
  have hc : Continuous Fourier.chi0Complex := Fourier.chi0Complex_contDiff.continuous
  have hi : Integrable Fourier.chi0Complex :=
    hc.integrable_of_hasCompactSupport (Fourier.chi0_hasCompactSupport.comp_left Complex.ofReal_zero)
  have hinv := hc.fourierInv_fourier_eq hi LemLin.integrable_fourier_chi0Complex
  have h0 : Fourier.chi0Complex 0 = 1 := by
    unfold Fourier.chi0Complex
    rw [Fourier.chi0_eq_one (by norm_num)]
    simp
  have hle : ‖𝓕⁻ (𝓕 Fourier.chi0Complex) 0‖ ≤ ∫ v : ℝ, ‖𝓕 Fourier.chi0Complex v‖ := by
    rw [Real.fourierInv_eq']
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext v
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hinv, h0, norm_one] at hle
  exact hle

/-! ## The `S = none` half -/

/-- **The `S = none` half of the weighted vine class bound at a record**, from the weighted flat estimate at that record
for every row selector. -/
theorem v5FrontierClassBoundNoneAt_of_flat (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMX P) : V5FrontierClassBoundOnAt (· = none) P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hcψ hpres hreal S hS hSpos hcoh
  subst hS
  have hc0 : 0 ≤ cψ := le_trans zero_le_one hcψ
  obtain ⟨αg, _, Mg, hMg, hvg⟩ := Flower.V5WA.presented_of_gPresented hc0 (hpres a.1.1)
  have hgle : ∀ x, ‖g a.1.1 x‖ ≤ cψ := fun x => by
    rw [← hvg]
    exact (Mg.norm_value_le x).trans hMg
  let I : VineEst.RowSel () := selW p (g a.1.1) cψ hcψ hgle (hreal a.1.1)
  have hB : ProfileBound P (truncF p h) (fun _ => B₀) p :=
    fun r hr => ⟨hB₀, by rw [truncF_eq h r hr]; exact hh r hr⟩
  have hF : ∀ k : ℕ, Summable fun z : Fin P.d → ℤ => |truncF p h k (wBar + latticePoint P.L z)| := by
    intro k
    by_cases hk : k ≤ p
    · simpa only [truncF, ite_eq_left hk] using P2.summable_layer_coset hB hd hL hk wBar
    · simp only [truncF, ite_eq_right hk, Pi.zero_apply, abs_zero, summable_zero]
  have hAl : ∀ x, stateLayer (startState B RD hG layer hLayer) x ≤ p := by
    rw [stateLayer_startState]
    exact hlay
  have hbr : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredFW p (g a.1.1) none G a
      (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar (VineC.modW lam)
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (rowSel := I) (p := p) (kind := kind) B RD hG layer hLayer
        (lvW B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (kparOf P.L P.γ P.δ (truncF p h) wBar)
          (Lvl.top B)) lam (G.sign a.toNode) (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    funext tt E
    rw [twistedRecenteredFW_none_eq p (g a.1.1) cψ hcψ hgle (hreal a.1.1)]
    refine (twistedRecenteredModCX_congr_F (rowSel := I) (startState B RD hG layer hLayer) hprime (chainStart B) hAl
      a P.L P.γ P.δ h (truncF p h) wBar lam _ (tt 0) (tt 1) (tt 2) _ _ _ _ (fun r hr => (truncF_eq h r hr).symm)).trans ?_
    exact congrFun (congrFun (twistedRecenteredModCX_bond_eq_flatFn (rowSel := I) (p := p) (kind := kind) B RD hG
      layer hLayer hprime lam (wdOf p (g a.1.1) cψ) cψ hc0
      (fun q q' k => by
        show ‖topPsi p (g a.1.1) q q' k‖ ≤ cψ
        unfold topPsi
        split_ifs
        · exact hgle k
        · simpa using hcψ)
      P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF) tt) E
  set mass : ℝ := cψ ^ (3 * U.card) * ∏ y ∈ regionDarts G U,
    nodeNorm (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain
      (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) cψ
      (Mole.dartNode G y) with hmassd
  have hpull : EnginePullback (Lvl.top B).region P.L wBar
      (lvW B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (kparOf P.L P.γ P.δ (truncF p h) wBar)
        (Lvl.top B)) mass :=
    enginePullback_bWN (startState B RD hG layer hLayer) (Lvl.top B).region B.isBlock P.L wBar p (g a.1.1) cψ hcψ
      ⟨αg, inferInstance, Mg, hMg, hvg⟩
  have hrow : ∏ y ∈ regionDarts G U,
      nodeNorm (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain
        (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) cψ
        (Mole.dartNode G y) =
      rowNorm cψ (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain R
        (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) :=
    prod_nodeNorm_regionDarts _ _ _ _ cψ hc0 B.isBlock R
  have hrowle := rowNorm_le hcψ (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain
    B.isBlock R (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer))
  have hrow0 : 0 ≤ rowNorm cψ (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain R
      (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) :=
    hrow ▸ Finset.prod_nonneg fun y _ => by unfold nodeNorm; split_ifs <;> positivity
  have hmass0 : 0 ≤ mass := by rw [hmassd, hrow]; positivity
  have hsp : I.weighted = true → I.p = p ∧ GPresented (32 * P.d) (I.g P.d) I.cψ := fun _ =>
    ⟨rfl, by show GPresented (32 * P.d) (gAt (g a.1.1) P.d) cψ; rw [gAt_self]; exact hpres a.1.1⟩
  have key := @H () I p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1
    centre wBar lam _ mass hmass0 hpull hcoh
  rw [hbr]
  refine key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hU1 : clLocalOrder1 R ≤ U.card := Finset.card_erase_le
  have hT := one_le_topFilterMass
  calc mass = cψ ^ (3 * U.card) * rowNorm cψ (startState B RD hG layer hLayer).data
        (startState B RD hG layer hLayer).plain R (stateLayer (startState B RD hG layer hLayer))
        (stateLayer_isLayering (startState B RD hG layer hLayer)) := by rw [hmassd, hrow]
    _ ≤ cψ ^ (3 * U.card) * cψ ^ (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R) :=
        mul_le_mul_of_nonneg_left hrowle (by positivity)
    _ = cψ ^ (3 * U.card + (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R)) := (pow_add _ _ _).symm
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) := pow_le_pow_right₀ hcψ (by omega)
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass :=
        le_mul_of_one_le_right (by positivity) hT

/-- **V5W-B: the `S = none` half of the weighted vine class bound** (supplement Lemma 5.3, V5 form), in the gate form of
the frozen `WTPrefix`, from main's selector certificate (`uniformTermCertKS`), main's leafwise regular-object gates,
`RealityAll` and INC-TOP's normalized incoherent gate. -/
theorem v5FrontierClassBoundNone : WTPrefix (V5FrontierClassBoundOnAt (· = none)) := by
  have H := vineFlatHalfMX_of_uniformCert uniformTermCertKS Spine.leafwise_coherent_approximation
    Spine.leafwise_incoherent_decay VineEstS5C.P1.realityAll IncTop.topIncoherentDecayGateR
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H1⟩ := H d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact v5FrontierClassBoundNoneAt_of_flat ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀, hL]) (H4 L hL)

/-- **The gate `V5FrontierClassBound`** from the `S ≠ none` half (the region-top stem filter, V5W-T). -/
theorem v5FrontierClassBound_of_top (hT : WTPrefix (V5FrontierClassBoundOnAt (· ≠ none))) : V5FrontierClassBound :=
  v5FrontierClassBound_of_halves v5FrontierClassBoundNone hT

end WaveTurbulence.Flower.V5WB
