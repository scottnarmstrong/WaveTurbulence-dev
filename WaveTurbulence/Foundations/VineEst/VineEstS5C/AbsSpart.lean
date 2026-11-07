/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ExtSExt

/-! # Uniform `L¹` bound of the native S-part `spart` over the upper-block decorations (V5 Step 4d part C, `hAbs`, leaf `sb`)

`tsum_localBound_le`: for an injective family of decorations indexed by `ι`, the sum of `localBound` is at most `baseConst`.
`norm_spart_le`, `integral_norm_spart_le`, `integrable_spart`: pointwise, integral and measurability bounds of `spart`.
**`sAbs_spart`**: `SAbs RS L base (spart ...) (baseConst ...)` for a block `S` with the CL parent pattern.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

theorem tsum_localBound_le {ι : Type*} (R : CLRegionData G S a b) (hF : HF D hG L F layer base)
    (xs : ι → (GNode G.tree → (Fin d → ℤ)))
    (hinj : Function.Injective fun (κ : ι) (p : ↥(clRegionalPairs hG S)) => xs κ (p.1.firstLeaf hG).toNode) :
    Summable (fun κ : ι => localBound D hG L γ δ F layer hLayer base R (xs κ)) ∧
      ∑' κ : ι, localBound D hG L γ δ F layer hLayer base R (xs κ) ≤ baseConst D hG L γ δ F layer hLayer base R := by
  let m : ↥(clRegionalPairs hG S) → (Fin d → ℤ) → ℝ := fun p x => pairBound D hG L γ δ F layer hLayer base p.1 x
  have hm0 : ∀ p x, 0 ≤ m p x := fun p x => by
    unfold m pairBound majSum
    exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  have hms : ∀ p, Summable (m p) := fun p =>
    (summable_majSum L F (nativeCoupleLayered D hG layer hLayer p.1) base
      (native_couple_plain D hG layer hLayer p.1) 0 (couple_hF_base hF p.1)).mul_left _
  obtain ⟨hs, hsb⟩ := tsum_pi_prod_le m hm0 hms
  set X : ι → (↥(clRegionalPairs hG S) → (Fin d → ℤ)) := fun κ p => xs κ (p.1.firstLeaf hG).toNode with hXdef
  set C' := ∏ v ∈ clInteriorBranches R, chainBound D hG L γ δ F layer hLayer base v with hC'
  have hC'0 : 0 ≤ C' := Finset.prod_nonneg fun v _ => by
    unfold chainBound
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun ℓ _ => tsum_nonneg fun n => abs_nonneg _)
  have h3 : ∀ κ : ι, localBound D hG L γ δ F layer hLayer base R (xs κ) = (∏ p, m p (X κ p)) * C' := by
    intro κ
    unfold localBound
    simp only [X, m]
    rw [Finset.prod_coe_sort (clRegionalPairs hG S)
      (fun p => pairBound D hG L γ δ F layer hLayer base p (xs κ (p.firstLeaf hG).toNode))]
  have hs2 := (hs.comp_injective hinj).mul_right C'
  refine ⟨hs2.congr fun κ => (h3 κ).symm, ?_⟩
  calc ∑' κ : ι, localBound D hG L γ δ F layer hLayer base R (xs κ)
      = ∑' κ : ι, (∏ p, m p (X κ p)) * C' := tsum_congr h3
    _ = (∑' κ : ι, ∏ p, m p (X κ p)) * C' := tsum_mul_right
    _ ≤ (∑' z : (↥(clRegionalPairs hG S) → (Fin d → ℤ)), ∏ p, m p (z p)) * C' := by
        refine mul_le_mul_of_nonneg_right ?_ hC'0
        exact tsum_comp_le_tsum_of_inj hs (fun z => Finset.prod_nonneg fun p _ => hm0 p (z p)) hinj
    _ ≤ (∏ p, ∑' x, m p x) * C' := mul_le_mul_of_nonneg_right hsb hC'0

end WaveTurbulence.VineEstS5C
