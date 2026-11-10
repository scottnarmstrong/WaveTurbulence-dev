/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Linear

/-! # P3: unrolling `psiFuel` over the levels into a finite multiset of product terms (V5 Step 4d part C)

`BundleExp`: the expansion of the bundle `psiSB` of one level into a finite family of summands (the pieces (a)-(c) and the remainder rows of
`bundle_decomp`, indexed by a finite type `Ch`), valid on a window `Win`.  `Lvl.terms BE m lv`: the multiset of product terms of the recursion
`Lvl.psiFuel`: at an operative level every inner term is multiplied by every summand of the bundle (the same shape as `psiStepSp`); inert levels
and the base give one term (the native row).  `Lvl.winOf`: the conjunction of the windows of the levels.  `Lvl.psiFuel_eq_terms`: on the window,
`psiFuel = ∑ terms`.  `card_terms_le`: the number of terms is at most `N ^ #members`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P3
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The expansion of the bundle `psiSB` of a level at the member `pstar` into finitely many summands, valid on the window `Win`
(the time window of `bundle_decomp`; the summands are the pieces (a)-(c) and the remainder rows, indexed by `Ch`). -/
structure BundleExp (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) where
  Ch : Type
  [fin : Fintype Ch]
  term : Ch → (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ
  Win : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → Prop
  eq : ∀ x u, Win x u →
    psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x u = ∑ c, term c x u

attribute [instance] BundleExp.fin

variable (p) in
/-- A family of bundle expansions, one for every level and member. -/
abbrev BundleExpFam (κ0 : KPar d) (hprime : IsPrimeGarden G) : Type 1 :=
  ∀ (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val), BundleExp (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime lv pstar hk

variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.VineEstS5C.P3
