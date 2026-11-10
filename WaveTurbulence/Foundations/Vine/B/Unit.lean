/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Meas
import Mathlib.Tactic

/-!
# VINE-B♯: absolute convergence of the modulated unit summand

For a CL region `R` and the source input summability `HF`, the modulated summand `lowModC · clLocalSummand` is
integrable, `κ ↦ ∫ ‖…‖` is summable with a bound `lbConst` independent of the boundary momenta and the clocks
(from V5's `localBound`, `summable_integral_norm_clLocalSummand`).
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

section Unit
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

/-- The uniform bound of the local decoration sum. -/
noncomputable def lbConst (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (R : CLRegionData G U a b) : ℝ :=
  (∏ p : ↥(clRegionalPairs hG U), ∑' x, pairBound D hG L γ δ F layer hLayer base p.1 x) *
    ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v

open scoped Classical in
theorem summable_tsum_localBound (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (hL : L ≠ 0) (β : Fin 4 → Mom d) :
    Summable (fun κ : CLLocalDecoration R L base β => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) ∧
      ∑' κ : CLLocalDecoration R L base β, localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) ≤
        lbConst D hG L γ δ F layer hLayer base R := by
  let m : ↥(clRegionalPairs hG U) → (Fin d → ℤ) → ℝ := fun p x => pairBound D hG L γ δ F layer hLayer base p.1 x
  have hm0 : ∀ p x, 0 ≤ m p x := fun p x => by
    unfold m pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  have hms : ∀ p, Summable (m p) := fun p =>
    (summable_majSum L F (nativeCoupleLayered D hG layer hLayer p.1) base
      (native_couple_plain D hG layer hLayer p.1) 0 (couple_hF_base hF p.1)).mul_left _
  obtain ⟨hs, hle⟩ := tsum_pi_prod_le m hm0 hms
  let X : CLLocalDecoration R L base β → (↥(clRegionalPairs hG U) → (Fin d → ℤ)) :=
    fun κ p => clExtendIndices R κ.1 (p.1.firstLeaf hG).toNode
  have hX : Function.Injective X := fun κ κ' h =>
    clLocalDecoration_ext_of_pairs hU R hG hL base β κ κ' fun p hp => congrFun h ⟨p, hp⟩
  have hfun : (fun κ : CLLocalDecoration R L base β => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) =
      fun κ => (∏ p, m p (X κ p)) * ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v := by
    funext κ
    unfold localBound
    simp only [X, m]
    rw [Finset.prod_coe_sort (clRegionalPairs hG U)
      (fun p => pairBound D hG L γ δ F layer hLayer base p (clExtendIndices R κ.1 (p.firstLeaf hG).toNode))]
  have hc0 : 0 ≤ ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v := by
    refine Finset.prod_nonneg fun v _ => ?_
    unfold chainBound
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)
  have h2 : Summable fun κ : CLLocalDecoration R L base β => ∏ p, m p (X κ p) := hs.comp_injective hX
  rw [hfun]
  refine ⟨h2.mul_right _, ?_⟩
  rw [tsum_mul_right]
  unfold lbConst
  refine mul_le_mul_of_nonneg_right (le_trans ?_ hle) hc0
  refine tsum_comp_le_tsum_of_inj hs (fun z => Finset.prod_nonneg fun i _ => hm0 i (z i)) hX |>.trans_eq' ?_
  rfl

theorem norm_integral_gUnit_le (R : CLRegionData G U a b) (hF : HF D hG L F layer base) (lam : ℝ)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) :
    ‖∫ τ : CLInternalTime R, lowModC R lam t τ *
      clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ‖ ≤
      localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have : (fun τ : CLInternalTime R => ‖lowModC R lam t τ *
      clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ‖) =
      fun τ => ‖clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ‖ := by
    funext τ; rw [norm_mul, norm_lowModC, one_mul]
  rw [this]
  exact integral_norm_clLocalSummand_le (γ := γ) (hLayer := hLayer) R hF β t κ

theorem norm_gUnit_le (R : CLRegionData G U a b) (hF : HF D hG L F layer base) (lam : ℝ)
    (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) :
    ‖lowModC R lam t τ * clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ‖ ≤
      (Set.pi Set.univ fun v : ↥(clInteriorBranches R) =>
        Set.Icc ((fun v => layer (D.coreBranch hG v).toNode) v.1 : ℝ)
          ((fun v => layer (D.coreBranch hG v).toNode) v.1 + 1)).indicator
        (fun _ => localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1)) τ := by
  rw [norm_mul, norm_lowModC, one_mul]
  refine (norm_clLocalSummand_le R hF β t κ τ).trans ?_
  exact Set.indicator_le_indicator_of_subset (localTimeDomain_subset_box R _ t)
    (fun _ => localBound_nonneg R _) τ

end Unit

end WaveTurbulence.VineB
