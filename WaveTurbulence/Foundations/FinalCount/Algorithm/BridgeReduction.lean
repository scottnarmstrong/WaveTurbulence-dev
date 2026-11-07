/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BridgeOrientation
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NormalGeometryStep
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeNormal
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeValidScales
import Mathlib.Tactic

/-! # Source rule one's complete concrete post counting problem -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]

structure BridgeReduction (s : State.{u,v} V) {d : ℕ} (L γ δ C1 g : ℝ) (w : Mom d)
    (A : (s.Dart → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) where
  target : State.{u,v} V
  admissible : (target.Dart → (Fin d → ℤ)) → Prop
  scales : Finset V → ℝ
  step : NormalGeometryStep s target 1
  molecule : target.graph.IsMolecule
  noLoops : AppbNoLoops target.graph
  noTripleBonds : AppbNoTripleBonds target.graph
  largeGap : ∀ ζ,admissible ζ → AppbLargeGap target.graph L w ζ g
  largeGapInherited : ∀ g',(∀ κ,A κ → AppbLargeGap s.graph L w κ g') →
    ∀ ζ,admissible ζ → AppbLargeGap target.graph L w ζ g'
  mateLabels : ∀ ζ,admissible ζ → ∀ x,ζ (target.graph.mate x) = ζ x
  scales_nonneg : ∀ S,0 ≤ scales S
  validLinkScales : ∀ c,AppbValidLinkScales s.graph L w A c P →
    AppbValidLinkScales target.graph L w admissible c scales
  deviation : IsDeviation (appbLinkCountA s.graph L γ δ C1 w A P)
    (appbLinkCountA target.graph L γ δ C1 w admissible scales) (ENNReal.ofReal (Real.log L^8))

/-- DH23 BR-N, including source priority one's outgoing representative,
actual safe post scales, and all inherited physical hypotheses. The
logarithmic deviation constant is independent of either carrier type. -/
theorem exists_bridge_reduction (s : State.{u,v} V) (hM : s.graph.IsMolecule)
    (hno : AppbNoLoops s.graph) (hnt : AppbNoTripleBonds s.graph)
    (hb : ∃ e : s.Dart,Degen.IsBridge s.graph e) {d : ℕ} {L δ C1 : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C1) (hlog : 1 ≤ Real.log L)
    (γ g : ℝ) (w : Mom d) (A : (s.Dart → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hP : ∀ S,0 ≤ P S)
    (hLG : ∀ κ,A κ → AppbLargeGap s.graph L w κ g) :
    Nonempty (BridgeReduction s L γ δ C1 g w A P) := by
  classical
  obtain ⟨e,he,ho⟩ := exists_outgoing_bridge s.graph hb
  obtain ⟨q,hq⟩ := appb_bridge_normal_bound s.graph hM e he hL γ δ C1 hlog hδ hC w A P hP
  refine ⟨{
    target := ofMolecule (eraseBond s.graph e)
    admissible := appbBridgePostAdmissibility s.graph e A q
    scales := appbBridgeScales s.graph e P
    step := .bridge s e he ho
    molecule := appb_eraseBond_isMolecule s.graph hM e
    noLoops := fun x => hno x.val
    noTripleBonds := noTripleBonds_eraseBond s.graph e hnt
    largeGap := ?_
    largeGapInherited := ?_
    mateLabels := ?_
    scales_nonneg := ?_
    validLinkScales := fun _ hv => hv.eraseBond e q
    deviation := hq }⟩
  · rintro ζ ⟨κ,hκ,hκq,hm,hr⟩
    rw [← hr]
    exact appb_eraseBond_largeGap s.graph e (hLG κ hκ)
  · intro g' hg ζ hζ
    obtain ⟨κ,hκ,hκq,hm,hr⟩ := hζ
    rw [← hr]
    exact appb_eraseBond_largeGap s.graph e (hg κ hκ)
  · rintro ζ ⟨κ,hκ,hκq,hm,hr⟩ x
    rw [← hr]
    exact hm x.val
  · intro S
    unfold appbBridgeScales
    split_ifs
    · exact hP S
    · exact le_rfl

end WaveTurbulence.Mole.AppbAlgorithm
