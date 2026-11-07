/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPrefixAnchor
public import WaveTurbulence.Foundations.VineEst.VineEstS2.FlowDegreeTwo

/-! # The next chart's actual two anchor labels retain the source gap -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}

/-- Incoming/outgoing labels at the shared atom give the same r for the
next ingredient. No nonzero-gap premise or independent gap witness is used. -/
theorem clPrefixAnchor_gap {E : Type*} [AddCommGroup E] {r : E}
    (hS : G.molecule.IsBlock S a b) (hT : G.molecule.IsBlock T b c)
    (RP : CLRegionData G S a b) (RT : CLRegionData G T b c) (hi : S ∩ T = {b})
    (k : FlowFiber G.molecule T b c E r) :
    k.1 (clPrefixAnchorBond hS hT RP RT hi)-k.1 (clPrefixCoanchorBond hS hT RP RT hi) = r := by
  let dp := clPrefixChildDart hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)
  let dn := clPrefixChildDart hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)
  have hp := clPrefixChildDart_spec hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)
  have hn := clPrefixChildDart_spec hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)
  have hsp : G.molecule.dartSign dp.1 = -1 := by
    have h := clPrefixChildDart_sign hS hT RP RT hi RP.positive (clRegionPositive_ne_kept RP)
    rw [RP.positive_sign] at h
    simpa only [Units.val_one,Int.cast_one] using h
  have hsn : G.molecule.dartSign dn.1 = 1 := by
    have h := clPrefixChildDart_sign hS hT RP RT hi RP.negative (clRegionNegative_ne_kept RP)
    rw [RP.negative_sign] at h
    simpa only [Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_neg] using h
  have hOp : G.molecule.out dp.1 = false := by
    by_cases ho : G.molecule.out dp.1 = true
    · have h := hsp
      simp only [Molecule.dartSign,ho,ite_true] at h
      norm_num at h
    · exact Bool.eq_false_of_not_eq_true ho
  have hOn : G.molecule.out dn.1 = true := by
    by_cases ho : G.molecule.out dn.1 = true
    · exact ho
    · have hf := Bool.eq_false_of_not_eq_true ho
      have h := hsn
      simp only [Molecule.dartSign,hf,Bool.false_eq_true,ite_false] at h
      norm_num at h
  have hT' := hT
  have hd := (Mole.block_joint_degrees G.molecule hT').1
  have hflow := flow_eq_outgoing_sub_incoming_of_deg_two G.molecule T b hd dn dp hn.1 hp.1 hOn hOp k.1
  have he : internalDartValue G.molecule T k.1 dn-internalDartValue G.molecule T k.1 dp = -r :=
    hflow.symm.trans k.2.1
  have hneg := congrArg (fun q : E => -q) he
  simpa only [neg_sub,neg_neg,internalDartValue,clPrefixAnchorBond,clPrefixCoanchorBond,
    clPrefixChildBond,dp,dn] using hneg

end WaveTurbulence.VineEstS2
