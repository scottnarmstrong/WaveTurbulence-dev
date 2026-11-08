/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5WT.FlatOut
public import WaveTurbulence.Foundations.Flower.V5WT.FlatT
public import WaveTurbulence.Foundations.Flower.V5WT.TopFilter
public import WaveTurbulence.Foundations.Flower.V5WB.Final

/-! # V5W-T: the `S ≠ none` half of the weighted vine class bound, and the gate

* `v5FrontierClassBoundSomeAt_of_flat`: at a record where the output-dependent weighted flat estimate holds for every
  selector, the pinned class kernel at `S = some s` is the selector class at `selW p (g a) cψ` with every member's
  top-weighted weight `bWT (wdOf p (g a) cψ) (topFilterWeight (some s))` (`twistedRecenteredFW_eq`), which is the
  weighted flat observable of the representative with the multiplier `lvWT (Lvl.top B)` (`classSumBT_eq_flat`); that
  multiplier is the product of the masked bond weight (engine pullback of mass `cψ^{3|U|}·rowNorm`,
  `enginePullback_bWN`) and the region-top stem filter (output-dependent pullback of mass `topFilterMass`,
  `topFilterPullbackStatement`, supplement Lemma 9.3), so its mass is at most `cψ^{9|U| + 4 n₂} · topFilterMass`.
* **`v5FrontierClassBoundSome : WTPrefix (V5FrontierClassBoundOnAt (· ≠ none))`**, from main's certificate for every
  selector (`uniformTermCertKS`), main's two leafwise gates, `RealityAll`, INC-TOP's gate, main's `sumint` with
  character mixtures and its output-dependent copy (T2, inside `vineFlatHalfMXOut_of_uniformCert`).
* **`v5FrontierClassBound : V5FrontierClassBound`** (= `V5WB.v5FrontierClassBound_of_top v5FrontierClassBoundSome`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence TTree Twist LFTwist RegRed Reg.Skeleton VineEstS2 VineEstS3 VineEstS4 VineEstS5B Links
  MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.Flower.V5WB
open WaveTurbulence.VineSpaceK (ClassMember EnginePullback)
open WaveTurbulence.VineSpaceB (regionDarts)
open WaveTurbulence.Flower.V5W (twistedRecenteredFW topFilterMass topFilterWeight V5FrontierClassBound
  V5FrontierClassBoundAt)
open WaveTurbulence.Flower.Stage1W (topPsi GPresented)
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine

theorem norm_topFilterWeight_le {d : ℕ} (s : ℝ) (z : Fin 4 → Mom d) : ‖topFilterWeight (some s) z‖ ≤ 1 := by
  have h : ∀ y : ℝ, ‖((WaveTurbulence.chi0 y : ℝ) : ℂ)‖ ≤ 1 := fun y => by
    have h0 : 0 ≤ WaveTurbulence.chi0 y := Real.smoothTransition.nonneg _
    have h1 : WaveTurbulence.chi0 y ≤ 1 := Real.smoothTransition.le_one _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  exact h _

/-- **The `S ≠ none` half of the weighted vine class bound at a record**, from the output-dependent weighted flat
estimate at that record for every row selector. -/
theorem v5FrontierClassBoundSomeAt_of_flat (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : ∀ {u : Unit} [_I : VineEst.RowSel u], VineFlatHalfMXOut P) : V5FrontierClassBoundOnAt (· ≠ none) P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    g cψ hcψ hpres hreal S hS hSpos hcoh
  obtain ⟨s, rfl⟩ := Option.ne_none_iff_exists'.mp hS
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
  have hbr : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredFW p (g a.1.1) (some s) G a
      (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar (VineC.modW lam)
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (rowSel := I) (p := p) (kind := kind) B RD hG layer hLayer
        (lvWT B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeight (some s))
          (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B))
        lam (G.sign a.toNode) (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    funext tt E
    rw [twistedRecenteredFW_eq p (g a.1.1) cψ hcψ hgle (hreal a.1.1) (some s)]
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
      (topFilterWeight (some s)) 1 zero_le_one (norm_topFilterWeight_le s)
      P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF) tt) E
  have hT := one_le_topFilterMass
  set mass : ℝ := cψ ^ (3 * U.card) * ∏ y ∈ regionDarts G U,
    nodeNorm (startState B RD hG layer hLayer).data (startState B RD hG layer hLayer).plain
      (stateLayer (startState B RD hG layer hLayer)) (stateLayer_isLayering (startState B RD hG layer hLayer)) cψ
      (Mole.dartNode G y) with hmassd
  have hpullB := enginePullback_bWN (startState B RD hG layer hLayer) (Lvl.top B).region B.isBlock P.L wBar p
    (g a.1.1) cψ hcψ ⟨αg, inferInstance, Mg, hMg, hvg⟩
  have hpullT := topFilterPullbackStatement (Lvl.top B).region P.L wBar (some s) hSpos
  have hpull : EnginePullbackOut (Lvl.top B).region P.L wBar
      (lvWT B RD hG layer hLayer (wdOf p (g a.1.1) cψ) (topFilterWeight (some s))
        (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B)) (mass * topFilterMass) :=
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
  have hT0 : 0 ≤ topFilterMass := le_trans zero_le_one hT
  have hmass0 : 0 ≤ mass * topFilterMass := by rw [hmassd, hrow]; positivity
  have hsp : I.weighted = true → I.p = p ∧ GPresented (32 * P.d) (I.g P.d) I.cψ := fun _ =>
    ⟨rfl, by show GPresented (32 * P.d) (gAt (g a.1.1) P.d) cψ; rw [gAt_self]; exact hpres a.1.1⟩
  have key := @H () I p hp hsp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1
    centre wBar lam _ (mass * topFilterMass) hmass0 hpull hcoh
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

/-- **V5W-T: the `S ≠ none` half of the weighted vine class bound** (supplement Lemma 5.3 with the region-top stem
filter of Lemma 9.3, V5 form), in the gate form of the frozen `WTPrefix`. -/
theorem v5FrontierClassBoundSome : WTPrefix (V5FrontierClassBoundOnAt (· ≠ none)) := by
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
  exact v5FrontierClassBoundSomeAt_of_flat ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀, hL]) (H4 L hL)

/-- **The weighted vine class bound** `V5FrontierClassBound` (V5W-0's statement), from its two halves. -/
theorem v5FrontierClassBound : V5FrontierClassBound :=
  v5FrontierClassBound_of_top v5FrontierClassBoundSome

end WaveTurbulence.Flower.V5WT
