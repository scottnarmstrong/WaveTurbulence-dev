/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPrefixAnchorOrigins
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOriginGeometry
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainOrigins
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOriginGeometry` (sha256 3736f8f94c76c031…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source-chain origin lifts preserve actual local incidence geometry -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}
variable {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
variable {RP : CLRegionData G S a b} {n : ℕ}

theorem prefixOriginLift_originAtΓ (B : CLChainAssemblyΓ γF G RP n)
    (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c) (hi : S ∩ T = {b})
    (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)
    (p : Bond G.molecule S ⊕ Fin 2) (v : GBranch G.tree) (out : Bool)
    (h : OriginAt G.molecule S b p v out) :
    OriginAt G.molecule (S ∪ T) c (prefixOriginLiftΓ B hT hi hU R p) v out := by
  cases p with
  | inl e => exact h
  | inr j =>
    obtain ⟨rfl,hout⟩ := h
    by_cases hj : j = 0
    · simp only [hj,ite_true] at hout
      subst out
      simp only [prefixOriginLiftΓ,hj,ite_true]
      exact clPrefixAnchor_originAt B.isBlock (memBlock hT) RP (B.terminalRegion hT hi hU R) hi
    · simp only [hj,ite_false] at hout
      subst out
      simp only [prefixOriginLiftΓ,hj,ite_false]
      exact clPrefixCoanchor_originAt B.isBlock (memBlock hT) RP (B.terminalRegion hT hi hU R) hi

end WaveTurbulence.GammaLow.Famb.VineEstS2
