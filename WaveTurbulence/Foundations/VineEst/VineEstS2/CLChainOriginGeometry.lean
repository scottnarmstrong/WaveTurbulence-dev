/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPrefixAnchorOrigins

/-! # Source-chain origin lifts preserve actual local incidence geometry -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ}

theorem terminalOriginLift_originAt (p : Bond G.molecule T ⊕ Fin 2)
    (v : GBranch G.tree) (out : Bool) (h : OriginAt G.molecule T c p v out) :
    OriginAt G.molecule (S ∪ T) c (terminalOriginLift p) v out := by
  cases p <;> exact h

theorem prefixOriginLift_originAt (B : CLChainAssembly G RP n)
    {X : VineType} (hT : G.molecule.IsVine X T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)
    (p : Bond G.molecule S ⊕ Fin 2) (v : GBranch G.tree) (out : Bool)
    (h : OriginAt G.molecule S b p v out) :
    OriginAt G.molecule (S ∪ T) c (prefixOriginLift B hT hi hU R p) v out := by
  cases p with
  | inl e => exact h
  | inr j =>
    obtain ⟨rfl,hout⟩ := h
    by_cases hj : j = 0
    · simp only [hj,ite_true] at hout
      subst out
      simp only [prefixOriginLift,hj,ite_true]
      exact clPrefixAnchor_originAt B.isBlock hT.1 RP (B.terminalRegion hT hi hU R) hi
    · simp only [hj,ite_false] at hout
      subst out
      simp only [prefixOriginLift,hj,ite_false]
      exact clPrefixCoanchor_originAt B.isBlock hT.1 RP (B.terminalRegion hT hi hU R) hi

end WaveTurbulence.VineEstS2
