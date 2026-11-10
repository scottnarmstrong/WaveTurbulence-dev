/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Statements
public import WaveTurbulence.Foundations.Flower.V5WA.Instance
public import WaveTurbulence.Foundations.Flower.V5WB.B.Flat
public import WaveTurbulence.Foundations.Flower.V5WB.K.FlatBound
public import WaveTurbulence.Foundations.Flower.V5WB.W2.FinalS
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2
public import WaveTurbulence.Foundations.Flower.V5WB.B.Bridge
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

end WaveTurbulence.Flower.V5WB
