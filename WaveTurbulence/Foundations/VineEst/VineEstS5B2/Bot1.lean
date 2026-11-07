/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.Final3

/-! # V5 Step 4d-B2: the bottom vine, part 1 (the `b`-factor of the summand of a whole chain region)

When the member `p*` is the bottom piece of the chain there is no lower block `T`: the lower joint `b = (placement p*).lower` is the
bottom joint of the whole region `(U, a, b)` and the boundary values `(g, h)` sit at its two excluded children.  The summand of the
region factors as `spart U a b * bFac`, where `bFac` is the contribution of the atom `b` itself (the interaction coefficient, the phase of
`b`, and the two time conditions `t₁ < u_b`, `t₂ < u_b` at the boundary children that are branches), all the rest being the S-part with
`S = U`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

open Classical in
/-- The two time conditions at the boundary children of the bottom joint (only for children that are branches). -/
@[expose] def bTimeOK (R : CLRegionData G U a b) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : Prop :=
  ((b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching → t 1 < u b) ∧
    ((b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching → t 2 < u b)

open Classical in
/-- **The `b`-factor** of the summand of a CL region: interaction coefficient and phase of the bottom joint, and the two boundary time
conditions. -/
@[expose] noncomputable def bFac (R : CLRegionData G U a b) (L γ δ : ℝ) (base : Mom d)
    (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ) : ℂ :=
  (epsBranch x b : ℂ) * phaseAtom L γ δ (G.sign b.toNode) (omegaNode G (cosetDecoration G L base x) b) (u b) *
    (if bTimeOK R t u then 1 else 0)

variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

open Classical in
/-- **The summand of a whole chain region is `spart U a b · bFac`.** -/
theorem clLocalSummand_eq_spart_bFac (R : CLRegionData G U a b) (hb : b ∈ U) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ)
    (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ =
      spart D hG L γ δ F layer hLayer base U a b (clExtendIndices R κ.1) (clLocalClock R t τ) *
        bFac R L γ δ base (clExtendIndices R κ.1) t (clLocalClock R t τ) := by
  unfold clLocalSummand
  set x := clExtendIndices R κ.1 with hx
  set u := clLocalClock R t τ with hu
  have hua : u a = t 0 := clLocalClock_upper R t τ
  have hdom : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t ↔
      DomS (fun v => layer (D.coreBranch hG v).toNode) U a u ∧ bTimeOK R t u := by
    unfold clLocalTimeDomain DomS bTimeOK
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun v hv => ?_, h2, h3⟩
      have := h1 ⟨v, hv⟩
      have e : u v = τ ⟨v, hv⟩ := clLocalClock_internal R t τ ⟨v, hv⟩
      rw [hua, e]
      exact this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun v => ?_, h2, h3⟩
      have := h1 v.1 v.2
      have e : u v.1 = τ v := clLocalClock_internal R t τ v
      rw [hua, e] at this
      exact this
  have he : (clRegionalEpsilon G U x : ℂ) = (clRegionalEpsilon G (U.erase b) x : ℂ) * (epsBranch x b : ℂ) := by
    unfold clRegionalEpsilon
    rw [← Finset.mul_prod_erase U (fun v => epsBranch x v) hb]
    push_cast
    ring
  have hp : clRegionalPhase G U L γ δ (cosetDecoration G L base x) u =
      clRegionalPhase G (U.erase b) L γ δ (cosetDecoration G L base x) u *
        phaseAtom L γ δ (G.sign b.toNode) (omegaNode G (cosetDecoration G L base x) b) (u b) := by
    unfold clRegionalPhase
    rw [← Finset.mul_prod_erase U (fun v => phaseAtom L γ δ (G.sign v.toNode)
      (omegaNode G (cosetDecoration G L base x) v) (u v)) hb]
    ring
  have hsp : starProd D hG L γ δ F layer hLayer base U a (u a) x u =
      clLocalStarProduct D hG R L γ δ F layer hLayer base x t τ := by
    rw [clLocalStarProduct_eq, hua]
  by_cases hτ : τ ∈ clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t
  · obtain ⟨hs, ht⟩ := hdom.mp hτ
    rw [Set.indicator_of_mem hτ]
    unfold spart bFac
    rw [if_pos hs, if_pos ht, he, hp, hsp]
    ring
  · rw [Set.indicator_of_notMem hτ]
    by_cases hs : DomS (fun v => layer (D.coreBranch hG v).toNode) U a u
    · have ht : ¬ bTimeOK R t u := fun h => hτ (hdom.mpr ⟨hs, h⟩)
      unfold bFac
      rw [if_neg ht]
      simp
    · unfold spart
      rw [if_neg hs]
      simp

end WaveTurbulence.VineEstS5B2
