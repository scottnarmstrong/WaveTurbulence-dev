/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOrigins
public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalDartOriginAt

/-! # The joined anchor origins retain their actual local directions -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

private theorem out_false_of_negative {V D : Type*} (M : Molecule V D) (d : D)
    (h : M.dartSign d = -1) : M.out d = false := by
  cases ho : M.out d
  · rfl
  · norm_num [Molecule.dartSign,ho] at h

private theorem out_true_of_positive {V D : Type*} (M : Molecule V D) (d : D)
    (h : M.dartSign d = 1) : M.out d = true := by
  cases ho : M.out d
  · norm_num [Molecule.dartSign,ho] at h
  · rfl

theorem clPrefixPositive_out (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) :
    G.molecule.out (clPrefixChildDart hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)).1 = false := by
  apply out_false_of_negative
  have h := clPrefixChildDart_sign hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)
  rw [RP.positive_sign] at h
  simpa only [Units.val_one,Int.cast_one] using h

theorem clPrefixNegative_out (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) :
    G.molecule.out (clPrefixChildDart hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)).1 = true := by
  apply out_true_of_positive
  have h := clPrefixChildDart_sign hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)
  rw [RP.negative_sign] at h
  simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_neg] using h

theorem clPrefixAnchor_originAt (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) :
    OriginAt G.molecule T c (.inl (clPrefixAnchorBond hS hT RP RT hi)) b false := by
  have he := internalDartBond_originAt G.molecule T c
    (clPrefixChildDart hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP))
  rw [(clPrefixChildDart_spec hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)).1,
    clPrefixPositive_out] at he
  exact he

theorem clPrefixCoanchor_originAt (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b}) :
    OriginAt G.molecule T c (.inl (clPrefixCoanchorBond hS hT RP RT hi)) b true := by
  have he := internalDartBond_originAt G.molecule T c
    (clPrefixChildDart hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP))
  rw [(clPrefixChildDart_spec hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)).1,
    clPrefixNegative_out] at he
  exact he

end WaveTurbulence.VineEstS2
