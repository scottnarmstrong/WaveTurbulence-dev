/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Fiber6
import Mathlib.Tactic

/-!
# VINE-B♯: the unit factor `HkM` and the summand of `outerValM`

`unitKernelM`: the unit factor of the per-mode identity, V5's modulated recentered kernel `clRecenteredLocalKernelModC`
of the unit with the profile `h(·, j₁, j₁)` and the modulation `λ_j`.  `unitKernelM_eq`: it is the recentering factor
times `coupling^{n_(1)} ζ` times the sum over local decorations of the time integral of `gUnit`.
`unitKernelM_clocks`: only the three exterior clocks `clocks τ' j` matter, and they are `clockOf ∘ hclk j`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- **The unit factor `HkM`** of the per-mode identity (V5's modulated recentered kernel, curried as S2's `HkM`). -/
noncomputable def unitKernelM (blk : J → CLBlock S) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) :
    J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ :=
  fun j lam t m => clRecenteredLocalKernelModC D hS (regionOf (blk j)) L γ δ (unitProfile blk h j) layer hLayer base
    (lam : ℝ) (t 0) (t 1) (t 2) (m 0) (m 1) (m 2) (m 3)

/-- The constant `coupling^{n_(1)} ζ` of unit `j`. -/
noncomputable def unitConst (blk : J → CLBlock S) (L γ δ : ℝ) (j : J) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 (regionOf (blk j)) * clLocalZeta (regionOf (blk j))

theorem unitKernelM_eq (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) (lam : ℤ) (t : Fin 3 → ℝ)
    (β : Fin 4 → Mom d) :
    unitKernelM blk D hS L γ δ h layer hLayer base j lam t β =
      recExp L γ δ (S.sign (blk j).upper.toNode) (t 0) β *
        (unitConst (d := d) blk L γ δ j *
          ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, ∫ τ : CLInternalTime (regionOf (blk j)),
            lowModC (regionOf (blk j)) (lam : ℝ) t τ *
              clLocalSummand D hS (regionOf (blk j)) L γ δ (unitProfile blk h j) layer hLayer base β t κ τ) := by
  have hb : ![β 0, β 1, β 2, β 3] = β := by funext i; fin_cases i <;> rfl
  have ht : ![t 0, t 1, t 2] = t := by funext i; fin_cases i <;> rfl
  unfold unitKernelM clRecenteredLocalKernelModC clLocalKernelModC recExp unitConst
  generalize hbb : ![β 0, β 1, β 2, β 3] = bb
  generalize htt : ![t 0, t 1, t 2] = tt'
  obtain rfl : bb = β := hbb.symm.trans hb
  obtain rfl : tt' = t := htt.symm.trans ht
  rfl

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem clock_pos_eq (hd : Disj blk) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (hb : ((blk j).lower.child (regionOf (blk j)).positive).1.2 ∈
      (S.tree ((blk j).lower.child (regionOf (blk j)).positive).1.1).branching) :
    clockOf Gsb tt τ' (Φ.hclk hd j 1) = Φ.clocks τ' j 1 :=
  (Φ.clock_hmom hd tt τ' j 2 hb).symm

theorem clock_neg_eq (hd : Disj blk) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (hb : ((blk j).lower.child (regionOf (blk j)).negative).1.2 ∈
      (S.tree ((blk j).lower.child (regionOf (blk j)).negative).1.1).branching) :
    clockOf Gsb tt τ' (Φ.hclk hd j 2) = Φ.clocks τ' j 2 :=
  (Φ.clock_hmom hd tt τ' j 3 hb).symm

theorem unitKernelM_clocks (hd : Disj blk) (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (tt : Fin w → ℝ) (τ' : GBranch Gsb.tree → ℝ) (j : J)
    (lam : ℤ) (β : Fin 4 → Mom d) :
    unitKernelM blk D hS L γ δ h layer hLayer base j lam (fun c => clockOf Gsb tt τ' (Φ.hclk hd j c)) β =
      unitKernelM blk D hS L γ δ h layer hLayer base j lam (Φ.clocks τ' j) β := by
  have h0 : clockOf Gsb tt τ' (Φ.hclk hd j 0) = Φ.clocks τ' j 0 := (Φ.clocks_zero hd τ' j).symm
  unfold unitKernelM
  simp only [h0]
  refine clRecenteredLocalKernelModC_congr D hS (regionOf (blk j)) L γ δ _ layer hLayer base _ _ _ _ _ _ _ _ _ _
    ?_ ?_
  · by_cases hb : ((blk j).lower.child (regionOf (blk j)).positive).1.2 ∈
        (S.tree ((blk j).lower.child (regionOf (blk j)).positive).1.1).branching
    · exact Or.inr (Φ.clock_pos_eq hd tt τ' j hb)
    · exact Or.inl hb
  · by_cases hb : ((blk j).lower.child (regionOf (blk j)).negative).1.2 ∈
        (S.tree ((blk j).lower.child (regionOf (blk j)).negative).1.1).branching
    · exact Or.inr (Φ.clock_neg_eq hd tt τ' j hb)
    · exact Or.inl hb

end SpliceShape

end WaveTurbulence.VineB
