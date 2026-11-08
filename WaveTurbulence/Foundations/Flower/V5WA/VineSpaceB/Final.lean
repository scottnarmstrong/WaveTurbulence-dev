/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Export
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.FlatPrefix
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.WeightedTrunc
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Uniform
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Trunc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Mono

/-! # V5-SPACE-EXT EXPORT: `V5BondClassBound` from the W2 certificate (R132/R135)

`v5BondClassBoundAt_of_flat`: the weighted flat estimate `VineFlatHalfMX` at a parameter record gives the bond-weighted
class bound `V5BondClassBoundAt` at that record: the literal class with each member's region bond weight is the
weighted flat observable of the representative (`twistedRecenteredModCX_bond_eq_flatFn`), whose multiplier has an
engine pullback with mass `cψ ^ (3 * |U|)` (`enginePullback_bondW`). `v5BondClassBound_of_uniformCert`: the gate form,
conditional only on the inputs of the existing weighted K export (`UniformTermCertTargetK`, the two leafwise
regular-object gates, `RealityAll`), with the constants of `WTPrefix` before the record. -/

@[expose] public section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.VineEstS5C.FlatMod VineSpaceK
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine Cut2A

/-- **The bond-weighted class bound at a record**, from the weighted flat estimate at that record. -/
theorem v5BondClassBoundAt_of_flat (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (H : VineFlatHalfMX P) : V5BondClassBoundAt P := by
  intro p hp h B₀ hB₀ hh w G U a b R n hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    ψ cψ hcψ htop hpres hcoh
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
  have hψ : ∀ q q' k, ‖ψ a.1.1 q q' k‖ ≤ cψ := by
    intro q q' k
    obtain ⟨α, _, M, hM, hv⟩ := hpres a.1.1 q q'
    rw [← hv]
    exact (M.norm_value_le k).trans hM
  have hcψ0 : 0 ≤ cψ := le_trans zero_le_one hcψ
  have hm : (fun z : ClassMember w (assemblySourceFamily B).CoreIndex => regionBondWeight (ψ a.1.1) P.L wBar z) =
      fun z : ClassMember w (assemblySourceFamily B).CoreIndex => bW (ψ a.1.1) (kparOf P.L P.γ P.δ (truncF p h) wBar) z.1 z.2.U := by
    funext z
    rw [regionBondWeight_eq]
    rfl
  have he := twistedRecenteredModCX_bond_eq_flatFn (p := p) (kind := kind) B RD hG layer hLayer hprime lam (ψ a.1.1)
    cψ hcψ0 hψ P.L P.γ P.δ (truncF p h) wBar (by linarith only [hL]) hF
  have he' : (fun (tt : Fin 3 → ℝ) (E : Fin 4 → Mom P.d) => twistedRecenteredModCX G a
      (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
      (fun z => regionBondWeight (ψ a.1.1) P.L wBar z) P.L P.γ P.δ h wBar lam
      (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
      (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) =
      flatFnRMX (p := p) (kind := kind) B RD hG layer hLayer
        (lvW B RD hG layer hLayer (ψ a.1.1) (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B)) lam (G.sign a.toNode)
        (kparOf P.L P.γ P.δ (truncF p h) wBar) hprime (G.sign a.toNode) := by
    rw [hm]
    refine Eq.trans ?_ he
    funext tt E
    exact twistedRecenteredModCX_congr_F (startState B RD hG layer hLayer) hprime (chainStart B) hAl a
      P.L P.γ P.δ h (truncF p h) wBar lam _
      (tt 0) (tt 1) (tt 2) _ _ _ _ (fun r hr => (truncF_eq h r hr).symm)
  rw [he']
  have hpull : EnginePullback (Lvl.top B).region P.L wBar
      (lvW B RD hG layer hLayer (ψ a.1.1) (kparOf P.L P.γ P.δ (truncF p h) wBar) (Lvl.top B)) (cψ ^ (3 * U.card)) :=
    enginePullback_bondW (Lvl.top B).region B.isBlock P.L wBar (ψ a.1.1) (layX (startState B RD hG layer hLayer)) p cψ hcψ
      (fun q q' hq => htop a.1.1 q q' hq) (hpres a.1.1)
  exact H hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer kind hcan hlay hord hl1 centre wBar lam
    _ (cψ ^ (3 * U.card)) (pow_nonneg hcψ0 _) hpull hcoh

/-- **`V5BondClassBound` (owner: V5-SPACE extension, R132/R135)**, conditional only on the inputs of the existing
weighted K export; the constants of the frozen `WTPrefix` precede the record. -/
theorem v5BondClassBound_of_uniformCert (hU : UniformTermCertTargetK)
    (hG : LeafwiseCoherentApproximationGate) (hI : LeafwiseIncoherentDecayGate)
    (hR : RealityAll) : V5BondClassBound := by
  have H := vineFlatHalfMX_of_uniformCert hU hG hI hR
  intro d hd γ hγ
  obtain ⟨η₀,hη₀,H1⟩ := H d hd γ hγ
  refine ⟨η₀,hη₀,?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁,hC₁,ν₀,hν₀,H2⟩ := H1 η hη φin hφin τ hτ φ hsol
  refine ⟨C₁,hC₁,ν₀,hν₀,?_⟩
  intro ν hν
  obtain ⟨δ₀,hδ₀,H3⟩ := H2 ν hν
  refine ⟨δ₀,hδ₀,?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂,hC₂,L₀,hL₀,H4⟩ := H3 δ hδ D hD htime
  refine ⟨C₂,hC₂,L₀,hL₀,?_⟩
  intro L hL
  exact v5BondClassBoundAt_of_flat ⟨d, γ, η, φin, τ, φ, C₁, ν, δ, D, C₂, L⟩
    (by change 1 ≤ d; omega) (by change 1 ≤ L; linarith only [hL₀,hL]) (H4 L hL)

end WaveTurbulence.VineSpaceB
