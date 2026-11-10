/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitFubini
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AbsConvLocal

/-! # Fubini form of the splitting of `K^U` at `b`, without the absolute-convergence premise (V5 Step 4b, P2.3)

`absConv_of_inputs`: the glued summands `fU` are absolutely convergent as soon as the inputs are absolutely summable on the
base coset (`HF`, the source premise on the inputs).  `clLocalKernel_split_fubini_of_inputs` is `clLocalKernel_split_fubini`
with `AbsConv` discharged: TARGET (tildeJ2) before the twist sum.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

section Inputs
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

/-- The glued summand is the summand of `U` at the corresponding local decoration. -/
theorem fU_eq (hL : L ≠ 0)
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (τ : CLInternalTime RU) :
    fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ =
      clLocalSummand D hG RU L γ δ F layer hLayer base ![e, f, g, h] ![t0, t1, t2]
        ((splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm p) τ := by
  have hx := splitLocalEquiv_symm_val hS hT hi hU RU RS RT hL base ![e, f, g, h] p
  exact (summand_split hS hT hi hU D hG γ δ F layer hLayer RU RS RT hL
    (clExtEquiv RT L base _ p.2).2.2 _ p.2 hx rfl ![t0, t1, t2] τ).symm

/-- **Absolute convergence of the glued summands** from the source input summability. -/
theorem absConv_of_inputs (hL : L ≠ 0) (hF : HF D hG L F layer base) :
    AbsConv hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h := by
  have hfun : ∀ p, fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p =
      fun τ => clLocalSummand D hG RU L γ δ F layer hLayer base ![e, f, g, h] ![t0, t1, t2]
        ((splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm p) τ :=
    fun p => funext fun τ => fU_eq hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL p τ
  refine ⟨fun p => ?_, ?_⟩
  · rw [hfun p]
    exact integrable_clLocalSummand RU hF _ _ _
  · have hs := (summable_integral_norm_clLocalSummand (hLayer := hLayer) (γ := γ) (δ := δ) hU RU hF hL
      ![e, f, g, h] ![t0, t1, t2]).comp_injective
      (splitLocalEquiv hS hT hi hU RU RS RT hL base ![e, f, g, h]).symm.injective
    refine hs.congr fun p => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
      congrArg norm (fU_eq hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h hL p τ).symm)

end Inputs

end WaveTurbulence.VineEstS4
