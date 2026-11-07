/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot4

/-! # V5 Step 4d-B2: the bottom vine, part 5 (`bFac_tw`)

See `Bot4`.  `bFac_tw` is the twist invariance of the `b`-factor.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

theorem mem_branching_iff_exists {w : ℕ} {F : Fin w → TTree} (n : GNode F) :
    n.1.2 ∈ (F n.1.1).branching ↔ ∃ b0 : GBranch F, b0.toNode = n :=
  ⟨fun h => ⟨⟨n.1, h⟩, rfl⟩, fun ⟨b0, hb⟩ => hb ▸ b0.2⟩

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

theorem branching_naive (n : GNode G.tree) :
    (naiveNodeEquiv G P n).1.2 ∈ ((unitTwistGarden G P).tree (naiveNodeEquiv G P n).1.1).branching ↔
      n.1.2 ∈ (G.tree n.1.1).branching := by
  rw [mem_branching_iff_exists, mem_branching_iff_exists]
  constructor
  · rintro ⟨b1, hb1⟩
    obtain ⟨b0, rfl⟩ := (coreBranchEquiv G P).surjective b1
    refine ⟨b0, ?_⟩
    apply (naiveNodeEquiv G P).injective
    exact (naiveNodeEquiv_branch G P b0).trans hb1
  · rintro ⟨b0, rfl⟩
    exact ⟨coreBranchEquiv G P b0, (naiveNodeEquiv_branch G P b0).symm⟩

variable {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')
include h

theorem stw_label_pos {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) :
    twistNodeLabels G P x ((eB P b).child RS'.positive) = x (b.child RS.positive) := by
  have hl := h.lower
  subst hl
  rw [stw_positive_eq P h]
  have := twistNodeLabels_lower_child G P x (freeSwap P.keep RS.positive)
  rw [if_neg (fun he => stw_positive_ne_keep P h ((freeSwap_eq_keep_iff G P _).mp he)),
    freeSwap_involutive P.keep] at this
  exact this

theorem stw_label_neg {d : ℕ} (x : GNode G.tree → (Fin d → ℤ)) :
    twistNodeLabels G P x ((eB P b).child RS'.negative) = x (b.child RS.negative) := by
  have hl := h.lower
  subst hl
  rw [stw_negative_eq P h]
  have := twistNodeLabels_lower_child G P x (freeSwap P.keep RS.negative)
  rw [if_neg (fun he => stw_negative_ne_keep P h ((freeSwap_eq_keep_iff G P _).mp he)),
    freeSwap_involutive P.keep] at this
  exact this

theorem stw_bTimeOK_iff (t : Fin 3 → ℝ) (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ)
    (hub : u' (eB P b) = u b) : bTimeOK RS' t u' ↔ bTimeOK RS t u := by
  have hl := h.lower
  subst hl
  have e1 := branching_naive P (P.lower.child RS.positive)
  have e2 := branching_naive P (P.lower.child RS.negative)
  rw [← stw_child_eb P h, ← stw_positive_eq P h] at e1
  rw [← stw_child_eb P h, ← stw_negative_eq P h] at e2
  unfold bTimeOK
  rw [hub]
  exact and_congr (imp_congr e1 Iff.rfl) (imp_congr e2 Iff.rfl)

end WaveTurbulence.VineEstS5B2
