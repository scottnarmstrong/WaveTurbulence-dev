/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB12
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm5
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the unit kernel `unitKernelM` is measurable in the clocks and uniformly bounded

`measurable_tsum_complex`; `measurable_unitKernelM_clocks`, `norm_unitKernelM_le` (`≤ ‖unitConst‖ · lbConst`, uniformly in
the clocks, the boundary momenta and the modulation).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB
  WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C
  WaveTurbulence.VineEstS5C.Cont MeasureTheory Filter Topology

theorem measurable_tsum_complex {α ι : Type*} [MeasurableSpace α] [Countable ι] (f : ι → α → ℂ)
    (hf : ∀ i, Measurable (f i)) (hs : ∀ x, Summable fun i => f i x) : Measurable fun x => ∑' i, f i x := by
  classical
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι)) (fun s => Finset.measurable_sum s fun i _ => hf i) ?_
  rw [tendsto_pi_nhds]
  intro x
  exact (hs x).hasSum

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

theorem norm_unitKernelM_le (D : ReconstructionData S) (hS : S.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) (j : J) (hF : HF D hS L (unitProfile blk h j) layer base)
    (lam : ℤ) (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) :
    ‖unitKernelM blk D hS L γ δ h layer hLayer base j lam t β‖ ≤
      ‖unitConst (d := d) blk L γ δ j‖ *
        lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) := by
  rw [unitKernelM_eq, norm_mul, norm_recExp, one_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  obtain ⟨hs, hle⟩ := summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock
    (regionOf (blk j)) hF hL β
  have hn : ∀ κ : CLLocalDecoration (regionOf (blk j)) L base β, ‖∫ τ : CLInternalTime (regionOf (blk j)),
      lowModC (regionOf (blk j)) (lam : ℝ) t τ *
        clLocalSummand D hS (regionOf (blk j)) L γ δ (unitProfile blk h j) layer hLayer base β t κ τ‖ ≤
      localBound D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) (clExtendIndices (regionOf (blk j)) κ.1) :=
    fun κ => norm_integral_gUnit_le (γ := γ) (hLayer := hLayer) (regionOf (blk j)) hF (lam : ℝ) β t κ
  calc _ ≤ ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, ‖∫ τ : CLInternalTime (regionOf (blk j)),
      lowModC (regionOf (blk j)) (lam : ℝ) t τ *
        clLocalSummand D hS (regionOf (blk j)) L γ δ (unitProfile blk h j) layer hLayer base β t κ τ‖ :=
        norm_tsum_le_tsum_norm (Summable.of_norm_bounded hs hn).norm
    _ ≤ ∑' κ : CLLocalDecoration (regionOf (blk j)) L base β, localBound D hS L γ δ (unitProfile blk h j) layer hLayer
        base (regionOf (blk j)) (clExtendIndices (regionOf (blk j)) κ.1) :=
        Summable.tsum_le_tsum hn (Summable.of_norm_bounded hs hn).norm hs
    _ ≤ _ := hle

end WaveTurbulence.Represents
