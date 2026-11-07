/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp9Fib
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowSum
public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt2
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
public import WaveTurbulence.Foundations.VineEst.CodeConj
public import WaveTurbulence.Foundations.VineEst.GardenConj

/-! # `ZpSurjStmt`: the exact statement that the packet ZP-SURJ (R51) must prove (F-ZPSURJ)

TARGET Step 4 (L1881-L1890): for the twisting vine `pstar` with the LF-twist class `Zp(A)` (the states reached from `A`
by one operation at `pstar`, or by skipping it), the exceptional pair `(T'_{u2}, Q'_{(u23,u0)})` ranges over the set `Bs`
of ALL coherent pairs described at the end of Def lftwist.  `replSum_decomp_ext` pairs, for one index `b = (Q, T)`, the
II-a state (lower joint sign `+1`, native objects `(conj Q, T)`) with the II-b state (sign `-1`, native objects
`(Q, conj T)`), and PL234 `reality_all` is a sum over the whole `CoherentPairCarrier p q q' n b`, so the leading
term (d) cancels only if `Zp(A)` realizes the whole carrier (R51).

Parameters of the carrier read off the state `A` (TARGET L1900-L1910, case `L_{u3} > L_{u4}` uses `B''`):
`zpQ4 A i = min (L_{u3}, L_{u4})` (the larger of the two parent layers of the exceptional pair, against the parent layer
of the lower joint) and `zpQ2 A i = L_{u2}` (the layer of the lower joint = the lone-leaf layer).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree

variable {w : ℕ} {ι : Type*}

/-- The exceptional couple, tree and their native layered gardens of the member `i` of the state `G`. -/
noncomputable def zpData (G : FamilyReconstruction w ι) (i : ι) :
    RegCpl × RegChain × LayeredGarden 2 × LayeredGarden 1 :=
  (G.data.couple (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained),
    G.data.tree (G.family.placement i).lower, (sigStar G i).2.1, (sigStar G i).2.2)

/-- The parent layers `(q, q')` of the exceptional pair of the member `i`. -/
noncomputable def zpPairQ (G : FamilyReconstruction w ι) (i : ι) : ℕ × ℕ :=
  pairQ G.data G.plain (stateLayer G) (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained)

/-- The parent layer and own layer of the lower joint of the member `i`. -/
noncomputable def zpBranchQ (G : FamilyReconstruction w ι) (i : ι) : ℕ × ℕ :=
  branchQ G.data G.plain (stateLayer G) (G.family.placement i).lower

/-- `min (L_{u3}, L_{u4})`. -/
noncomputable def zpQ4 (G : FamilyReconstruction w ι) (i : ι) : ℕ :=
  min (max (zpPairQ G i).1 (zpPairQ G i).2) (zpBranchQ G i).1

/-- `L_{u2}`. -/
noncomputable def zpQ2 (G : FamilyReconstruction w ι) (i : ι) : ℕ := (zpBranchQ G i).2

/-- The layer of the root of the positive tree of a layered couple. -/
noncomputable def cplRootLayer (LQ : LayeredGarden 2) : ℕ := LQ.layer (GNode.root LQ.garden.tree 0)

/-- The layer of the root of a layered tree. -/
noncomputable def treeRootLayer (LX : LayeredGarden 1) : ℕ := LX.layer (GNode.root LX.garden.tree 0)

/-- Half of the combined order of the exceptional pair of the member `i` (`n` of Prop layerreg2). -/
noncomputable def zpN (G : FamilyReconstruction w ι) (i : ι) : ℕ :=
  ((sigStar G i).2.1.garden.order + (sigStar G i).2.2.garden.order) / 2

/-- The combined number of layer-`p` branching nodes of the exceptional pair of the member `i`. -/
noncomputable def zpTop (p : ℕ) (G : FamilyReconstruction w ι) (i : ι) : Option ℕ :=
  some (topBranchCount (sigStar G i).2.1 p + topBranchCount (sigStar G i).2.2 p)

variable {p : ℕ} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
  (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)

open Classical in
/-- The parent layers `(q, q')` of the carrier-side couple: those of the native couple for a II-b state, swapped for a II-a
state (conjugation exchanges the two roots). -/
noncomputable def zpQQ (G : FamilyReconstruction w ι) (i : ι) : ℕ × ℕ :=
  if nuOf G i = -1 then zpPairQ G i else ((zpPairQ G i).2, (zpPairQ G i).1)

/-- The carrier at the parameters of `A`: `CoherentPairCarrier p L4 L2 n b` (TARGET `B''`). -/
def ZpCarrier (p : ℕ) (A : FamilyReconstruction w ι) (pstar : ι)
    (c : RegCpl × RegChain × LayeredGarden 2 × LayeredGarden 1) : Prop :=
  CoherentPairCarrier p (zpQ4 A pstar) (zpQ2 A pstar) (zpN A pstar) (zpTop p A pstar) c.1 c.2.1 c.2.2.1 c.2.2.2

open Classical in
/-- The carrier-side couple of a state: the native couple of a II-b state (sign `-1`), the conjugate of the native couple of
a II-a state (sign `+1`), which is the coherent couple `Q` of TARGET (replaceterm1). -/
noncomputable def zpObjC (G : FamilyReconstruction w ι) (i : ι) : LayeredGarden 2 :=
  if nuOf G i = -1 then (sigStar G i).2.1 else conjLayered (sigStar G i).2.1 (Equiv.swap (0 : Fin 2) 1)

open Classical in
/-- The carrier-side tree: the conjugate of the native tree of a II-b state, the native tree of a II-a state. -/
noncomputable def zpObjT (G : FamilyReconstruction w ι) (i : ι) : LayeredGarden 1 :=
  if nuOf G i = -1 then conjLayered (sigStar G i).2.2 (Equiv.refl (Fin 1)) else (sigStar G i).2.2

open Classical in
/-- The code of the carrier-side couple. -/
noncomputable def zpCodeC (G : FamilyReconstruction w ι) (i : ι) : RegCpl :=
  if nuOf G i = -1 then (zpData G i).1 else conjCpl (zpData G i).1

open Classical in
/-- The code of the carrier-side tree. -/
noncomputable def zpCodeT (G : FamilyReconstruction w ι) (i : ι) : RegChain :=
  if nuOf G i = -1 then conjChain (zpData G i).2.1 else (zpData G i).2.1

/-- The carrier element of a state (of either sign). -/
noncomputable def zpCarrierOf (G : FamilyReconstruction w ι) (i : ι) :
    RegCpl × RegChain × LayeredGarden 2 × LayeredGarden 1 :=
  (zpCodeC G i, zpCodeT G i, zpObjC G i, zpObjT G i)

/-- Both root layers of the carrier-side objects are `<= L4 = min (L_{u3}, L_{u4})`. -/
def ZpRootsLE (A : FamilyReconstruction w ι) (G : FamilyReconstruction w ι) (i : ι) : Prop :=
  cplRootLayer (zpObjC G i) ≤ zpQ4 A i ∧ treeRootLayer (zpObjT G i) ≤ zpQ4 A i

/-- The states of `Zp(A)` of sign `σ` with both roots `<= L4`. -/
def zpSet (p : ℕ) (kind : Bool) (pstar : ι) (J : Set ι) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) (σ : ℤˣ) :
    Set (ST w ι pstar J) :=
  {G | G ∈ zpFinset p kind pstar J A sp0 hA ∧ nuOf G.1 pstar = σ ∧ ZpRootsLE A G.1 pstar}

/-- **`ZpSurj`**: the exact statement of the packet ZP-SURJ (R51), TARGET Step 4 L1881-L1923.
* `coherent`: the carrier-side exceptional couple and tree (`zpObjC`, `zpObjT`) of every state of `Zp(A)` are coherent at the
  parent layers read off the state (Def lftwist: "coherent, with the exact structure of Prop layerreg1");
* `twin`: the states of sign `-1` with roots `<= L4` (II-b) and those of sign `+1` (II-a) are in bijection `τ`, the
  II-a state carrying the conjugate couple and tree (`IsConjugateCouple`, `IsConjugateTree`, `conjCpl`, `conjChain`):
  the "twin" (`Zp = {sk, sk'} × Bs` with independent ranges);
* `carrier`: the II-b states with roots `<= L4` realize EXACTLY the coherent pair carrier
  `CoherentPairCarrier p L4 L2 n b` (of PL234 `reality_all`), as the bijection `G ↦ (Q, conj T, ...)`.
Injectivity of `G ↦ sigStar G pstar` on `Zp(A)` is `zp_eq_of_sigStar` (Cls6Zp) and is not part of the statement. -/
structure ZpSurj (p : ℕ) (kind : Bool) (pstar : ι) (J : Set ι) (A : FamilyReconstruction w ι)
    (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton) : Prop where
  coherent : ∀ G ∈ zpFinset p kind pstar J A sp0 hA,
    IsCoherentCoupleAt p (zpQQ G.1 pstar).1 (zpQQ G.1 pstar).2 (zpCodeC G.1 pstar) (zpObjC G.1 pstar) ∧
    IsCoherentTreeAt p (zpBranchQ G.1 pstar).1 (zpBranchQ G.1 pstar).2 (zpCodeT G.1 pstar) (zpObjT G.1 pstar)
  twin : ∃ τ : ST w ι pstar J → ST w ι pstar J,
    Set.BijOn τ (zpSet p kind pstar J A sp0 hA (-1)) (zpSet p kind pstar J A sp0 hA 1) ∧
    ∀ G ∈ zpSet p kind pstar J A sp0 hA (-1),
      IsConjugateCouple (sigStar G.1 pstar).2.1 (sigStar (τ G).1 pstar).2.1 ∧
      IsConjugateTree (sigStar G.1 pstar).2.2 (sigStar (τ G).1 pstar).2.2 ∧
      (zpData (τ G).1 pstar).1 = conjCpl (zpData G.1 pstar).1 ∧
      (zpData (τ G).1 pstar).2.1 = conjChain (zpData G.1 pstar).2.1
  carrier : Set.BijOn (fun G : ST w ι pstar J => zpCarrierOf G.1 pstar) (zpSet p kind pstar J A sp0 hA (-1))
    {c | ZpCarrier p A pstar c}

end WaveTurbulence.VineEstS5C
