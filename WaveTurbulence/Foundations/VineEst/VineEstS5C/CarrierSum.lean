/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ZpSurjStmt
public import Mathlib.Algebra.BigOperators.Finprod

/-! # The carrier `finsum` of PL234 `reality_all` as a finite sum over states (V5 Step 4d part C, WP-B)

`carrier_finsum`: for a finite set `S` of tuples `(Q, X, LQ, LX)`, the nested `finsum` over the four binders with the guard
`(Q, X, LQ, LX) ∈ S` is the `finsum` over `S`.  `carrier_sum_eq`: for the bijection of `ZpSurj.carrier`, it is the finite sum over the
II-b states with carrier-side roots `<= L4`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ}

theorem carrier_finsum (S : Set (RegCpl × RegChain × LayeredGarden w × LayeredGarden 1)) (hS : S.Finite)
    (f : RegCpl → RegChain → LayeredGarden w → LayeredGarden 1 → ℂ) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden w) (LX : LayeredGarden 1) (_ : (Q, X, LQ, LX) ∈ S),
        f Q X LQ LX) = ∑ᶠ c ∈ S, f c.1 c.2.1 c.2.2.1 c.2.2.2 := by
  classical
  set g : RegCpl × RegChain × LayeredGarden w × LayeredGarden 1 → ℂ :=
    fun c => if c ∈ S then f c.1 c.2.1 c.2.2.1 c.2.2.2 else 0 with hg
  have hsupp : Function.support g ⊆ S := by
    intro c hc
    by_contra h
    exact hc (by simp [hg, h])
  have hfin : (Function.support g).Finite := hS.subset hsupp
  have h3 := finsum_curry₃ g hfin
  have hslice : ∀ (Q : RegCpl) (X : RegChain),
      (∑ᶠ p : LayeredGarden w × LayeredGarden 1, g (Q, X, p)) =
        ∑ᶠ (LQ : LayeredGarden w) (LX : LayeredGarden 1), g (Q, X, LQ, LX) := by
    intro Q X
    refine finsum_curry (fun p : LayeredGarden w × LayeredGarden 1 => g (Q, X, p)) ?_
    refine (hS.image (fun c => c.2.2)).subset ?_
    intro p hp
    have : (Q, X, p) ∈ Function.support g := hp
    exact ⟨_, hsupp this, rfl⟩
  have e1 : (∑ᶠ c ∈ S, f c.1 c.2.1 c.2.2.1 c.2.2.2) = ∑ᶠ c, g c := by
    rw [finsum_mem_def]
    refine finsum_congr fun c => ?_
    by_cases h : c ∈ S <;> simp [hg, h, Set.indicator]
  rw [e1, h3]
  refine finsum_congr fun Q => finsum_congr fun X => ?_
  rw [hslice]
  refine finsum_congr fun LQ => finsum_congr fun LX => ?_
  simp [hg, finsum_eq_if]


section
variable {ι : Type*} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The finset of II-b states of `Zp(A)` with carrier-side roots `<= L4`. -/
noncomputable def zpMinusFin (p : ℕ) (kind : Bool) (pstar : ι) (J : Set ι) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) : Finset (ST w ι pstar J) :=
  (zpFinset p kind pstar J A sp0 hA).filter fun G => nuOf G.1 pstar = -1 ∧ ZpRootsLE A G.1 pstar

theorem coe_zpMinusFin (p : ℕ) (kind : Bool) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton) :
    (zpMinusFin p kind pstar J A sp0 hA : Set (ST w ι pstar J)) = zpSet p kind pstar J A sp0 hA (-1) := by
  classical
  ext G
  simp [zpMinusFin, zpSet]

/-- **The carrier `finsum` of `reality_all` is the finite sum over the II-b states with roots `<= L4`.** -/
theorem carrier_sum_eq (p : ℕ) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hbij : Set.BijOn (fun G : ST w ι pstar J => zpCarrierOf G.1 pstar) (zpSet p kind pstar J A sp0 hA (-1))
      {c | ZpCarrier p A pstar c})
    (f : RegCpl → RegChain → LayeredGarden 2 → LayeredGarden 1 → ℂ) :
    (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Q X LQ LX),
        f Q X LQ LX) =
      ∑ G ∈ zpMinusFin p kind pstar J A sp0 hA, f (zpCarrierOf G.1 pstar).1 (zpCarrierOf G.1 pstar).2.1
        (zpCarrierOf G.1 pstar).2.2.1 (zpCarrierOf G.1 pstar).2.2.2 := by
  classical
  have hfin : ({c | ZpCarrier p A pstar c} : Set _).Finite := by
    rw [← hbij.image_eq]
    refine Set.Finite.image _ ?_
    rw [← coe_zpMinusFin p kind A sp0 hA]
    exact Finset.finite_toSet _
  have h1 := carrier_finsum {c | ZpCarrier p A pstar c} hfin f
  have h2 : (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) Q X LQ LX),
        f Q X LQ LX) = ∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
        (_ : (Q, X, LQ, LX) ∈ {c | ZpCarrier p A pstar c}), f Q X LQ LX := rfl
  rw [h2, h1, ← hbij.image_eq, finsum_mem_image hbij.injOn, ← coe_zpMinusFin p kind A sp0 hA, finsum_mem_coe_finset]

end
end WaveTurbulence.VineEstS5C
