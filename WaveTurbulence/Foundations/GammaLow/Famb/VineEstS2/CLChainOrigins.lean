/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChartEquations
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLPrefixAnchorGap
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOrigins
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChartEquations
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainOrigins` (sha256 663445a8522a0460…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Literal origin transport across source-chain concatenation -/

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
variable {RP : CLRegionData G S a b} {n : ℕ} (B : CLChainAssemblyΓ γF G RP n)
variable (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c) (hi : S ∩ T = {b})
variable (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c)

noncomputable def prefixOriginLiftΓ : Bond G.molecule S ⊕ Fin 2 → Bond G.molecule (S ∪ T) ⊕ Fin 2
  | .inl e => .inl (includeBond Finset.subset_union_left e)
  | .inr j => .inl (includeBond Finset.subset_union_right
      (if j = 0 then B.terminalAnchor hT hi hU R else
        clPrefixCoanchorBond B.isBlock (memBlock hT) RP (B.terminalRegion hT hi hU R) hi))

theorem terminalOriginLift_valueΓ {E : Type} [AddCommGroup E] {r : E}
    (g : E) (k : FlowFiber G.molecule (S ∪ T) a c E r) (p : Bond G.molecule T ⊕ Fin 2) :
    origin G.molecule (S ∪ T) k.1 g r (terminalOriginLift p) =
      origin G.molecule T (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k).1 g r p := by
  cases p <;> rfl

theorem prefixOriginLift_valueΓ {E : Type} [AddCommGroup E] {r : E}
    (g : E) (k : FlowFiber G.molecule (S ∪ T) a c E r) (p : Bond G.molecule S ⊕ Fin 2) :
    let kT := restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k
    origin G.molecule (S ∪ T) k.1 g r (prefixOriginLiftΓ B hT hi hU R p) =
      origin G.molecule S (restrictFlowFiber_left (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k).1
        (kT.1 (B.terminalAnchor hT hi hU R)) r p := by
  cases p with
  | inl e => rfl
  | inr j =>
    dsimp only [prefixOriginLiftΓ,origin]
    by_cases hj : j = 0
    · simp only [hj,ite_true]
      rfl
    · simp only [hj,ite_false]
      have he := clPrefixAnchor_gap B.isBlock (memBlock hT) RP (B.terminalRegion hT hi hU R) hi
        (restrictFlowFiber_right (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU k)
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm)

end WaveTurbulence.GammaLow.Famb.VineEstS2
