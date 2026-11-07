/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsConvLocal

/-! # The base obligations of `hAbs`: uniform `L¹` bound and joint measurability of the native summand (V5 Step 4d part C)

`tsum_integral_norm_clLocalSummand_le`: the uniform total of the `L¹` norms of the native summands over the decorations of a CL region is at most
`∏_p ∑_x pairBound_p(x) · ∏_v chainBound_v` (no dependence on the exterior times and momenta).  `uAbs_psiNat`: `UAbs` of `psiNat`.
`measT_psiNat`: `psiNat` is jointly measurable in the exterior times and the clock.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

/-- The uniform bound of the native summand total. -/
noncomputable def baseConst (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (R : CLRegionData G U a b) : ℝ :=
  (∏ p : ↥(clRegionalPairs hG U), ∑' x : Fin d → ℤ, pairBound D hG L γ δ F layer hLayer base p.1 x) *
    ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v

theorem baseConst_nonneg (R : CLRegionData G U a b) :
    0 ≤ baseConst D hG L γ δ F layer hLayer base R := by
  unfold baseConst
  refine mul_nonneg (Finset.prod_nonneg fun p _ => tsum_nonneg fun x => ?_) (Finset.prod_nonneg fun v _ => ?_)
  · unfold pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  · unfold chainBound
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)

theorem tsum_integral_norm_clLocalSummand_le (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (hL : L ≠ 0) (boundary : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    ∑' κ : CLLocalDecoration R L base boundary,
      ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ ≤
      baseConst D hG L γ δ F layer hLayer base R := by
  let m : ↥(clRegionalPairs hG U) → (Fin d → ℤ) → ℝ := fun p x => pairBound D hG L γ δ F layer hLayer base p.1 x
  have hm0 : ∀ p x, 0 ≤ m p x := fun p x => by
    unfold m pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  have hms : ∀ p, Summable (m p) := fun p =>
    (summable_majSum L F (nativeCoupleLayered D hG layer hLayer p.1) base
      (native_couple_plain D hG layer hLayer p.1) 0 (couple_hF_base hF p.1)).mul_left _
  obtain ⟨hs, hsb⟩ := tsum_pi_prod_le m hm0 hms
  let X : CLLocalDecoration R L base boundary → (↥(clRegionalPairs hG U) → (Fin d → ℤ)) :=
    fun κ p => clExtendIndices R κ.1 (p.1.firstLeaf hG).toNode
  have hX : Function.Injective X := fun κ κ' h =>
    clLocalDecoration_ext_of_pairs hU R hG hL base boundary κ κ' fun p hp => congrFun h ⟨p, hp⟩
  set C' := ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v with hC'
  have h2 := (hs.comp_injective hX).mul_right C'
  have h3 : ∀ κ : CLLocalDecoration R L base boundary,
      localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) = (∏ p, m p (X κ p)) * C' := by
    intro κ
    unfold localBound
    simp only [X, m]
    rw [Finset.prod_coe_sort (clRegionalPairs hG U)
      (fun p => pairBound D hG L γ δ F layer hLayer base p (clExtendIndices R κ.1 (p.firstLeaf hG).toNode))]
  have hs3 : Summable fun κ : CLLocalDecoration R L base boundary =>
      localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) := h2.congr fun κ => (h3 κ).symm
  have hnn : ∀ κ : CLLocalDecoration R L base boundary, 0 ≤ ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖ :=
    fun _ => integral_nonneg fun _ => norm_nonneg _
  have hC'0 : 0 ≤ C' := Finset.prod_nonneg fun v _ => by
    unfold chainBound
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)
  calc ∑' κ : CLLocalDecoration R L base boundary,
        ∫ τ, ‖clLocalSummand D hG R L γ δ F layer hLayer base boundary t κ τ‖
      ≤ ∑' κ : CLLocalDecoration R L base boundary, localBound D hG L γ δ F layer hLayer base R (clExtendIndices R κ.1) :=
        (summable_integral_norm_clLocalSummand (hLayer := hLayer) (γ := γ) (δ := δ) hU R hF hL boundary t).tsum_le_tsum
          (fun κ => integral_norm_clLocalSummand_le R hF boundary t κ) hs3
    _ = ∑' κ : CLLocalDecoration R L base boundary, (∏ p, m p (X κ p)) * C' := tsum_congr h3
    _ = (∑' κ : CLLocalDecoration R L base boundary, ∏ p, m p (X κ p)) * C' := tsum_mul_right
    _ ≤ (∑' z : (↥(clRegionalPairs hG U) → (Fin d → ℤ)), ∏ p, m p (z p)) * C' := by
        refine mul_le_mul_of_nonneg_right ?_ hC'0
        exact tsum_comp_le_tsum_of_inj hs (fun z => Finset.prod_nonneg fun p _ => hm0 p (z p)) hX
    _ ≤ (∏ p, ∑' x, m p x) * C' := mul_le_mul_of_nonneg_right hsb hC'0


/-- **`UAbs` of the native summand**, uniform in the exterior times and momenta. -/
theorem uAbs_psiNat (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hF : HF D hG L F layer base) (hL : L ≠ 0) :
    UAbs R L base (psiNat D hG R L γ δ F layer hLayer base) (baseConst D hG L γ δ F layer hLayer base R) := by
  intro t β
  have hfun : ∀ κ : CLLocalDecoration R L base β,
      (fun τ : CLInternalTime R => psiNat D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t (clLocalClock R t τ)) =
        fun τ => clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ := fun κ =>
    funext fun τ => (clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base β t κ τ).symm
  refine ⟨fun κ => ?_, ?_, ?_⟩
  · rw [hfun κ]; exact integrable_clLocalSummand R hF β t κ
  · refine (summable_integral_norm_clLocalSummand (hLayer := hLayer) (γ := γ) (δ := δ) hU R hF hL β t).congr fun κ => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
      congrArg norm (clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base β t κ τ))
  · refine le_of_eq_of_le (tsum_congr fun κ => ?_) (tsum_integral_norm_clLocalSummand_le hU R hF hL β t)
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
      congrArg norm (clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base β t κ τ).symm)

end WaveTurbulence.VineEstS5C
