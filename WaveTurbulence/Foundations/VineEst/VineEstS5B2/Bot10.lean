/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot9

/-! # V5 Step 4d-B2: the bottom vine, part 10 (the kernels of the states of the twist class, in the chart of the source)

`clLocalKernel_same`: the kernel of a state with the same skeleton (skip or FALSE choice) of the whole chain region, as `c ζ ∑' ∫ sameIntB`.
`clLocalKernel_tw`: the kernel of the twisted chain region, as `-(c ζ ∑' ∫ twIntB)` in the chart of the source (the decorations correspond
by `decEquiv`, the times by `tEquivS`, and `ζ' = -ζ`).
`BOKd`: integrable in the times for every decoration, with summable `L¹` norms in the decorations, and its transport along `decEquiv`/`tEquivS`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

/-- Integrable in the times for every decoration, with summable `L¹` norms in the decorations (local decorations of a region). -/
@[expose] def BOKd {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (β : Fin 4 → Mom d) (g : CLLocalDecoration R L base β → CLInternalTime R → ℂ) : Prop :=
  (∀ κ, Integrable (g κ)) ∧ Summable fun κ => ∫ τ, ‖g κ τ‖

theorem BOKd.const_mul {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {g : CLLocalDecoration R L base β → CLInternalTime R → ℂ}
    (hg : BOKd R L base β g) (c : ℂ) : BOKd R L base β (fun κ τ => c * g κ τ) := by
  refine ⟨fun κ => (hg.1 κ).const_mul c, ?_⟩
  have : ∀ κ, ∫ τ, ‖c * g κ τ‖ = ‖c‖ * ∫ τ, ‖g κ τ‖ := fun κ => by
    simp_rw [norm_mul]; rw [integral_const_mul]
  simp_rw [this]
  exact hg.2.mul_left _

theorem BOKd.congr {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {L : ℝ} {base : Mom d} {β : Fin 4 → Mom d} {g g' : CLLocalDecoration R L base β → CLInternalTime R → ℂ}
    (hg : BOKd R L base β g) (e : g = g') : BOKd R L base β g' := e ▸ hg

theorem BOKd_of_inputs {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (D : ReconstructionData G) (hG : G.IsPlain)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer)
    (base : Mom d) (hL : L ≠ 0) (hF : HF D hG L F layer base) (β : Fin 4 → Mom d) (t : Fin 3 → ℝ) :
    BOKd R L base β (fun κ τ => clLocalSummand D hG R L γ δ F layer hLayer base β t κ τ) :=
  ⟨fun κ => integrable_clLocalSummand R hF β t κ, summable_integral_norm_clLocalSummand hU R hF hL β t⟩

section Kernel
variable {w d : ℕ} {G : Garden w} (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)

variable (P : CorePlacement G) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}
  {RS' : CLRegionData (unitTwistGarden G P) (twistedAtoms G P S) (eB P a) (eB P b)} (h : STw P RS RS')

end Kernel

end WaveTurbulence.VineEstS5B2
