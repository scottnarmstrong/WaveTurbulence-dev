/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB7
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the mode form of the skeleton expression (engine form)

`skelVal_slotFn_eq_tsum_outerValM`: `skelVal(slotFn) = Σ'_ξ w_ξ · outerValM(amp ξ, frq ξ, …, unitKernelM)`: VINE-B♯'s per-mode
identity (`skelVal_modal_eq_outerValM`, with `hsum` from `tsum_ampBound_mode_le`) summed over the modes `ξ` of the slot family.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineB WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS4 MeasureTheory

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}
variable (Φ : SpliceShape blk Gsb)

open scoped Classical in
theorem hasSum_skelVal_outerValM (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL0 : 0 < L)
    (γ δ : ℝ) (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (selSk : GenDecoration S d roots 0 → Prop)
    (Zw : GenDecoration Gsb d roots 0 → ℝ)
    (hZ : ∀ κ : GenDecoration S d roots 0, (if selSk κ then (1 : ℝ) else 0) = Zw (Φ.resDec hS hd κ))
    (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base)
    (fam : SlotFam Gsb d) (Box : ReplacementSlot Gsb → Set (Fin 2 → ℝ))
    (hexp : ∀ s', ∀ ts ∈ Box s', ∀ x, HasSum (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts)
      (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (Φ.iota hS hSb s') ts x))
    (hbox : ∀ τ ∈ coreTimeDomainW (fun b => layer (D.coreBranch hS b).toNode) tt, ∀ s',
      slotTs hS tt τ (Φ.iota hS hSb s') ∈ Box s') :
    HasSum (fun ξ : ∀ s, fam.Λ s => ((modeWt fam ξ : ℝ) : ℂ) *
      outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb
        (fun s' => fam.a s' (ξ s')) (fun s' => fam.m s' (ξ s')) (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd)
        (unitKernelM blk D hS L γ δ h layer hLayer base))
      (skelVal D hS L γ δ base roots tt layer selSk
        (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer)) := by
  have hL : L ≠ 0 := hL0.ne'
  have key := hasSum_skelVal_modes Φ hd hS hSb hL0 γ δ base D layer hLayer h tt selSk Zw hZ hF fam Box hexp hbox
  refine key.congr_fun fun ξ => ?_
  rw [Φ.skelVal_modal_eq_outerValM hd hS hSb hL γ δ base D layer hLayer h tt (fun s' x => fam.a s' (ξ s') x)
    (fun s' => fam.m s' (ξ s')) selSk Zw hZ hF (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1]

end WaveTurbulence.Represents
