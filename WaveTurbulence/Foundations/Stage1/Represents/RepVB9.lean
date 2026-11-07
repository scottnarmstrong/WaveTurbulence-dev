/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB8
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the source summability `HF` of the unit profiles

`HF_of_snorm`: V5's source input summability from the spatial norm bound of the profile at every layer `≤ p`;
`hF_unit_of_bounded`: for the unit profiles `unitProfile blk h j` of a type family bounded at layer `≤ p`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB
  WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineEstS4

theorem HF_of_snorm {w d : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) {L : ℝ} (hL1 : 1 ≤ L)
    (hd : 1 ≤ d) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ) (base : Mom d) (p : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hlay : ∀ x, layer x ≤ p) (hF : ∀ q ≤ p, SNormR (40 * d) (40 * d) (F q) ≤ ENNReal.ofReal C) :
    HF D hG L F layer base :=
  fun _ _ => summable_abs_coset_of_SNormR hL1 (by omega) hC (F _) (hF _ (hlay _)) base

theorem hF_unit_of_bounded {w d : ℕ} {S : Garden w} {J : Type} {blk : J → CLBlock S} (D : ReconstructionData S)
    (hS : S.IsPlain) {L : ℝ} (hL1 : 1 ≤ L) (hd : 1 ≤ d) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (base : Mom d) (p : ℕ) {C : ℝ} (hC : 0 ≤ C) (hlay : ∀ x, layer x ≤ p)
    (hh : ∀ q j j', q ≤ p → SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal C) (j : J) :
    HF D hS L (unitProfile blk h j) layer base :=
  HF_of_snorm D hS hL1 hd _ layer base p hC hlay fun q hq => hh q _ _ hq

end WaveTurbulence.Represents
