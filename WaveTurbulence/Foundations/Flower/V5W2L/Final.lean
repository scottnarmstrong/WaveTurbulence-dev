/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W2L.TopFilter
public import WaveTurbulence.Foundations.Flower.V5W2L.Class
public import WaveTurbulence.Foundations.Flower.V5WT.Final

/-! # V5W-2L: V5's frontier class bound with a finite product of top filters, and the bridge

* `v5FrontierClassBoundAtL_of_flat`: at a record where V5W-T's output-dependent weighted flat estimate holds for every
  selector, the class kernel with the product filter `topFilterWeightL S` is the selector class at `selW p (g a) cψ`
  with every member's weight `bWT (wdOf p (g a) cψ) (topFilterWeightL S)` (`twistedRecenteredFWL_eq`), which is the
  weighted flat observable with the multiplier `lvWT (Lvl.top B)` (`V5WT.twistedRecenteredModCX_bondT_eq_flatFn`, any
  top weight of norm `≤ 1`, here `norm_topFilterWeightL_le`).  That multiplier is the masked bond weight (engine
  pullback of mass `cψ^{3|U|}·rowNorm`, `V5WB.enginePullback_bWN`) times the product filter (output-dependent pullback
  of mass `topFilterMass ^ S.length`, `topFilterPullbackL`), so its mass is at most
  `cψ^{9|U| + 4 n₂} · topFilterMass ^ S.length`.
* **`v5FrontierClassBoundL : V5FrontierClassBoundL`** (= `WTPrefix V5FrontierClassBoundAtL`), from exactly the inputs
  of V5W-T's `v5FrontierClassBoundSome` (main's certificate for every selector, main's two leafwise gates,
  `RealityAll`, INC-TOP's gate, main's `sumint` with character mixtures and V5W-T's output-dependent copy).
* **Bridge** `v5FrontierClassBoundAt_of_L : V5FrontierClassBoundAtL P → V5W.V5FrontierClassBoundAt P`: the old
  statement is the `S.length ≤ 1` instance `S.toList` (`twistedRecenteredFWL_toList`; `topFilterMass ^ 0 = 1 ≤
  topFilterMass`, `topFilterMass ^ 1 = topFilterMass`); and its prefix form `v5FrontierClassBound_of_L`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5W2L
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.Flower.V5WT (EnginePullbackOut enginePullbackOut_mul VineFlatHalfMXOut lvWT
  twistedRecenteredModCX_bondT_eq_flatFn vineFlatHalfMXOut_of_uniformCert)
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback)
open WaveTurbulence.VineSpaceB (regionDarts)
open WaveTurbulence.Flower.V5W (twistedRecenteredFW topFilterMass topFilterWeight V5FrontierClassBound
  V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine

/-- **V5's frontier class bound with a product of top filters at a record**, from the output-dependent weighted flat
estimate at that record for every row selector. -/
theorem v5FrontierClassBoundAtL_of_flat (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOut P) : V5FrontierClassBoundAtL P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hcψ hpres hreal S _hSpos hcoh
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
  have hbr : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredFWL p (g a.1.1) S G a
      (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar (VineC.modW lam)
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (rowSel := I) (p := p) (kind := kind) B RD hG layer hLayer
        (lvWT B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeightL S)
          (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B))
        lam (G.sign a.toNode) (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    funext tt E
    rw [twistedRecenteredFWL_eq p (g a.1.1) cψ hcψ hgle (hreal a.1.1) S]
    refine (twistedRecenteredModCX_congr_F (rowSel := I) (startState B RD hG layer hLayer) hprime (chainStart B) hAl
      a P.L P.γ P.δ h (truncF p h) wBar lam _ (tt 0) (tt 1) (tt 2) _ _ _ _ (fun r hr => (truncF_eq h r hr).symm)).trans ?_
    exact congrFun (congrFun (twistedRecenteredModCX_bondT_eq_flatFn (rowSel := I) (p := p) (kind := kind) B RD hG
      layer hLayer hprime lam (wdOf p (g a.1.1) cψ) cψ hc0
      (fun q q' k => by
        show ‖topPsi p (g a.1.1) q q' k‖ ≤ cψ
        unfold topPsi
        split_ifs
        · exact hgle k
        · simpa using hcψ)
      (topFilterWeightL S) 1 zero_le_one (norm_topFilterWeightL_le S)
      P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF) tt) E
  have hT := one_le_topFilterMass
  set mass : ℝ := cψ ^ (3 * U.card) * ∏ y ∈ regionDarts G U,
    nodeNorm (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain
      (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) cψ
      (Mole.dartNode G y) with hmassd
  have hpullB := enginePullback_bWN (startState B RD hG layer hLayer) (Lvl.top B).region B.isBlock P.L wBar p
    (g a.1.1) cψ hcψ ⟨αg, inferInstance, Mg, hMg, hvg⟩
  have hpullT := topFilterPullbackL (Lvl.top B).region P.L wBar S
  have hpull : EnginePullbackOut (Lvl.top B).region P.L wBar
      (lvWT B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeightL S)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B)) (mass * topFilterMass ^ S.length) :=
    enginePullbackOut_mul (Lvl.top B).region P.L wBar hpullB hpullT
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
  have hT0 : 0 ≤ topFilterMass ^ S.length := pow_nonneg (le_trans zero_le_one hT) _
  have hmass0 : 0 ≤ mass * topFilterMass ^ S.length := by rw [hmassd, hrow]; positivity
  have hsp : I.weighted = true → I.p = p ∧ GPresented (32 * P.d) (I.g P.d) I.cψ := fun _ =>
    ⟨rfl, by show GPresented (32 * P.d) (gAt (g a.1.1) P.d) cψ; rw [gAt_self]; exact hpres a.1.1⟩
  have key := @H () I p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1
    centre wBar lam _ (mass * topFilterMass ^ S.length) hmass0 hpull hcoh
  rw [hbr]
  refine key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hU1 : clLocalOrder1 R ≤ U.card := Finset.card_erase_le
  refine mul_le_mul_of_nonneg_right ?_ hT0
  calc mass = cψ ^ (3 * U.card) * rowNorm cψ (startState B RD hG layer hLayer).data
        (startState B RD hG layer hLayer).plain R (stateLayer (startState B RD hG layer hLayer))
        (stateLayer_isLayering (startState B RD hG layer hLayer)) := by rw [hmassd, hrow]
    _ ≤ cψ ^ (3 * U.card) * cψ ^ (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R) :=
        mul_le_mul_of_nonneg_left hrowle (by positivity)
    _ = cψ ^ (3 * U.card + (2 * clLocalOrder2 RD hG R + 2 * clLocalOrder1 R)) := (pow_add _ _ _).symm
    _ ≤ cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) := pow_le_pow_right₀ hcψ (by omega)

/-- **V5W-2L: V5's frontier class bound with a finite product of region-top stem filters** (supplement Lemma 5.3
with Lemma 9.3 once per factor, V5 form), in the gate form of the frozen `WTPrefix`. -/
theorem v5FrontierClassBoundL : V5FrontierClassBoundL := by
  have H := vineFlatHalfMXOut_of_uniformCert uniformTermCertKS Spine.leafwise_coherent_approximation
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
  exact v5FrontierClassBoundAtL_of_flat ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀, hL]) (H4 L hL)

/-! ## The bridge: the single-filter statement is the `S.length ≤ 1` instance -/

end WaveTurbulence.Flower.V5W2L
