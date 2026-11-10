/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitLocal
public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitKernel

/-! # Fubini form of the splitting of `K^U` at the joint `b` (V5 Step 4b, P2.3, TARGET (tildeJ2) before the twist sum)

`fU` is the summand of `K^U` at a glued decoration `(xS, κ)`.  Assuming its absolute convergence
(`AbsConv`: every `fU p` integrable and `∑_p ∫‖fU p‖ < ∞`), `clLocalKernel_split_fubini` separates the factors:
`K^U = coupling^{n₁(S)} ζ_S ∑_{xS} ∫_{σ ∈ times(S)} spart(xS, σ) · K^T(σ_b, t₁, t₂; E(xS), F(xS), g, h) dσ`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
variable {w d : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

instance countable_CLLocalDecoration {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d) :
    Countable (CLLocalDecoration R L base boundary) := by
  unfold CLLocalDecoration
  infer_instance

section Fubini
variable (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
  (hU : G.molecule.IsBlock (S ∪ T) a c) (RU : CLRegionData G (S ∪ T) a c) (RS : CLRegionData G S a b)
  (RT : CLRegionData G T b c) (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
  (t0 t1 t2 : ℝ) (e f g h : Mom d)

/-- The summand of `K^U` at the glued decoration `(xS, κ)`, as in `clLocalKernel_split_sigma`. -/
@[expose] noncomputable def fU
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h))
    (τ : CLInternalTime RU) : ℂ :=
  spart D hG L γ δ F layer hLayer base S a b p.1.1 (clLocalClock RU ![t0, t1, t2] τ) *
    clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
      (tT b RU ![t0, t1, t2] τ) p.2 (restrT hS hT hi hU RU RT τ)

/-- Absolute convergence of the glued summands: each is integrable and the integrals of the norms are summable. -/
@[expose] def AbsConv : Prop :=
  (∀ p, Integrable (fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p)) ∧
    Summable (fun p => ∫ τ, ‖fU hS hT hi hU RU RS RT D hG L γ δ F layer hLayer base t0 t1 t2 e f g h p τ‖)

/-- The time-`b` kernel integrand of `T`, integrated over the times of `T`. -/
@[expose] noncomputable def JT
    (p : Σ xS : ExtS RS L base e f, CLLocalDecoration RT L base (bdT RT L base xS.1 g h)) (u : ℝ) : ℂ :=
  ∫ ρ : CLInternalTime RT, clLocalSummand D hG RT L γ δ F layer hLayer base (bdT RT L base p.1.1 g h)
    ![u, t1, t2] p.2 ρ

end Fubini

end WaveTurbulence.VineEstS4
