/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot5

/-! # V5 Step 4d-B2: the bottom vine, part 6 (`bFac_tw`)

The twist invariance of the `b`-factor: the sign of `b` and the resonance factor `Ω_b` both change sign, the interaction coefficient is
unchanged under the conservation at `b`, and the boundary time conditions are unchanged.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

theorem keep_cases : P.keep = 0 ∨ P.keep = 2 := by
  have h1 := P.outer
  generalize P.keep = k at h1 ⊢
  fin_cases k <;> simp_all

/-- The labels of the twisted lower joint and its children, in terms of the original labels. -/
theorem lower_labels {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) :
    (P.keep = 0 →
      twistNodeLabels G P x (eB P P.lower).toNode = x (P.lower.child 0) ∧
      twistNodeLabels G P x ((eB P P.lower).child 0) = x P.lower.toNode ∧
      twistNodeLabels G P x ((eB P P.lower).child 1) = x (P.lower.child 2) ∧
      twistNodeLabels G P x ((eB P P.lower).child 2) = x (P.lower.child 1)) ∧
    (P.keep = 2 →
      twistNodeLabels G P x (eB P P.lower).toNode = x (P.lower.child 2) ∧
      twistNodeLabels G P x ((eB P P.lower).child 0) = x (P.lower.child 1) ∧
      twistNodeLabels G P x ((eB P P.lower).child 1) = x (P.lower.child 0) ∧
      twistNodeLabels G P x ((eB P P.lower).child 2) = x P.lower.toNode) := by
  have hb : twistNodeLabels G P x (eB P P.lower).toNode = x (P.lower.child P.keep) := by
    rw [show (eB P P.lower).toNode = (coreBranchEquiv G P P.lower).toNode from rfl, twistNodeLabels_lower, P.child]
  have hc := fun i => twistNodeLabels_lower_child G P x i
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [hk] at hb
    refine ⟨hb, ?_, ?_, ?_⟩
    · have := hc 0; rw [hk] at this; simp at this; exact this
    · have := hc 1; rw [hk] at this; simp [freeSwap, Equiv.swap_apply_def] at this; exact this
    · have := hc 2; rw [hk] at this; simp [freeSwap, Equiv.swap_apply_def] at this; exact this
  · rw [hk] at hb
    refine ⟨hb, ?_, ?_, ?_⟩
    · have := hc 0; rw [hk] at this; simp [freeSwap, Equiv.swap_apply_def] at this; exact this
    · have := hc 1; rw [hk] at this; simp [freeSwap, Equiv.swap_apply_def] at this; exact this
    · have := hc 2; rw [hk] at this; simp at this; exact this

variable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
include h

open Classical in
theorem stw_bFac {d : ℕ} (L γ δ : ℝ) (base : Mom d) (x : GNode G.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ)
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ) (hub : u' (eB P b) = u b)
    (hcons : x b.toNode = x (b.child 0) - x (b.child 1) + x (b.child 2)) :
    bFac RS' L γ δ base (twistNodeLabels G P x) t u' = bFac RS L γ δ base x t u := by
  have hl := h.lower
  have hT := stw_bTimeOK_iff P h t u' u hub
  subst hl
  have hs : (unitTwistGarden G P).sign (eB P P.lower).toNode = -G.sign P.lower.toNode := by
    rw [show (eB P P.lower).toNode = (coreBranchEquiv G P P.lower).toNode from rfl, coreBranchEquiv_sign, if_pos rfl]
  have hlab := lower_labels P x
  unfold bFac
  have hiff : (if bTimeOK RS' t u' then (1 : ℂ) else 0) = if bTimeOK RS t u then 1 else 0 := by
    simp only [hT]
  rw [hiff, hub, hs]
  congr 1
  congr 1
  · rcases keep_cases P with hk | hk
    · obtain ⟨e0, e1, e2, e3⟩ := hlab.1 hk
      have hc : x P.lower.toNode = x (P.lower.child 0) - x (P.lower.child 1) + x (P.lower.child 2) := hcons
      have := epsCoef_swap1 (x (P.lower.child 0)) (x (P.lower.child 1)) (x (P.lower.child 2))
      rw [← hc] at this
      unfold epsBranch
      rw [e1, e2, e3, this]
    · obtain ⟨e0, e1, e2, e3⟩ := hlab.2 hk
      have hc : x P.lower.toNode = x (P.lower.child 0) - x (P.lower.child 1) + x (P.lower.child 2) := hcons
      have := epsCoef_swap2 (x (P.lower.child 0)) (x (P.lower.child 1)) (x (P.lower.child 2))
      rw [← hc] at this
      unfold epsBranch
      rw [e1, e2, e3, this]
  · have hom : omegaNode (unitTwistGarden G P)
        (cosetDecoration (unitTwistGarden G P) L base (twistNodeLabels G P x)) (eB P P.lower) =
        -omegaNode G (cosetDecoration G L base x) P.lower := by
      unfold omegaNode resFactor cosetDecoration
      rcases keep_cases P with hk | hk
      · obtain ⟨e0, e1, e2, e3⟩ := hlab.1 hk
        rw [e0, e1, e2, e3]
        ring
      · obtain ⟨e0, e1, e2, e3⟩ := hlab.2 hk
        rw [e0, e1, e2, e3]
        ring
    rw [hom]
    exact phaseAtom_neg L γ δ _ _ _

end WaveTurbulence.VineEstS5B2
