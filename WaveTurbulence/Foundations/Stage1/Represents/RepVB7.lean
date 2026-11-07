/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB6
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: `skelVal(slotFn)` is the weighted sum of the modal skeleton expressions

`hasSum_skelVal_modes` (the statement of the interchange in Lean; proof from `hasSum_tsum_interchange` and the glued
domination `kBound`).
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
theorem hasSum_skelVal_modes (hd : Disj blk) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {L : ℝ} (hL0 : 0 < L) (γ δ : ℝ)
    (base : Mom d) (D : ReconstructionData S) (layer : GNode (D.forest hS) → ℕ)
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
      skelVal D hS L γ δ base roots tt layer selSk
        (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
          (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))))
      (skelVal D hS L γ δ base roots tt layer selSk
        (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer)) := by
  have hL : L ≠ 0 := hL0.ne'
  have hcnt : ∀ s, Countable (fam.Λ s) := fam.cnt
  have hwt : Summable (modeWt fam) :=
    (hasSum_prod_real (fun s l => fam.w s l) (fun s l => fam.w_nn s l) (fun s => fam.w_sum s)).summable
  have key := hasSum_tsum_interchange (modeWt fam) (modeWt_nonneg fam) hwt (Φ.decSplit hS hd hL base roots)
    (fun ξ p => Φ.kBound hSb L γ δ base D hS layer hLayer h (fun s' x => fam.a s' (ξ s') x) p)
    (fun ξ p => Φ.kBound_nonneg hSb L γ δ base D hS layer hLayer h _ p)
    (fun ξ => Φ.summable_kBound hS hSb hL γ δ base D layer hLayer h (roots := roots) _ hF
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1)
    ((((⌊2 * L⌋₊ + 2) ^ d) ^ Fintype.card (SourcePair Gsb) : ℕ) *
      ∏ j, lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)))
    (fun ξ => tsum_kBound_le Φ hS hSb hL γ δ base D layer hLayer h _ hF
      (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).1 _ (tsum_ampBound_mode_le fam hSb L hL0 base roots ξ).2)
    (fun ξ κ => skelTerm D hS L γ δ base roots tt layer selSk
      (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer
        (fun s' x => fam.a s' (ξ s') x) (fun s' => fam.m s' (ξ s'))) κ)
    (fun κ => skelTerm D hS L γ δ base roots tt layer selSk
      (slotFn D hS L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer) κ)
    (fun ξ κ => by
      have := Φ.norm_skelTerm_symm_le hd hS hSb hL γ δ base D layer hLayer h tt (fun s' x => fam.a s' (ξ s') x)
        (fun s' => fam.m s' (ξ s')) selSk Zw hZ hF ((Φ.decSplit hS hd hL base roots) κ)
      rwa [Equiv.symm_apply_apply] at this)
    (fun κ => by
      have := hasSum_skelTerm_modes Φ hd hS hSb hL γ δ base D layer hLayer h tt selSk hF fam Box hexp hbox
        ((Φ.decSplit hS hd hL base roots) κ).1 ((Φ.decSplit hS hd hL base roots) κ).2
      have hκ : Φ.glueDec hS hd hL base ((Φ.decSplit hS hd hL base roots) κ).1
          ((Φ.decSplit hS hd hL base roots) κ).2 = κ := (Φ.decSplit hS hd hL base roots).symm_apply_apply κ
      rwa [hκ] at this)
  have h2 := key.mul_left ((coupling d L γ δ : ℂ) ^ S.order * S.zeta)
  rw [skelVal_eq]
  convert h2 using 1
  funext ξ
  rw [skelVal_eq]
  ring

end WaveTurbulence.Represents
