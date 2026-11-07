/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ZpSurjStmt
public import WaveTurbulence.Foundations.VineEst.RowSel.Coherent

/-! # V5W-B (ruling F2), B2: the exceptional rows of the `Zp(A)` states are plain

`ZpSurj.coherent` says that the carrier-side exceptional couple and tree of every state of `Zp(A)` are coherent
(`IsCoherentCoupleAt p … (zpCodeC G i) (zpObjC G i)`, `IsCoherentTreeAt p … (zpCodeT G i) (zpObjT G i)`).  The
carrier-side objects are the native ones or their conjugates, according to the sign `nuOf G i` of the lower joint.  By the
bridges of `RowSel/Coherent` (direct and conjugate orientation) the native exceptional rows have incoherency index `0`
(`coupleIncoh_eq_zero_of_zp`, `treeIncoh_eq_zero_of_zp`), so the selected exceptional rows `rowQ κ G i`, `rowT κ G i`
are the plain `KQstar`/`KTstar` rows for every selector (`rowQ_eq_of_zp`, `rowT_eq_of_zp`, and the `ZpSurj` forms
`rowQ_zp`, `rowT_zp`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEst
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.RegRed WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.LGSpine WaveTurbulence.ConjCoh TTree

variable {w : ℕ} {ι : Type*}

/-- The native exceptional couple of a state decodes its code. -/
theorem zp_couple_decodes (G : FamilyReconstruction w ι) (i : ι) :
    (G.data.couple (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained)).Decodes (sigStar G i).2.1.garden := by
  show (G.data.couple _).Decodes (nativeCoupleLayered G.data G.plain (stateLayer G) (stateLayer_isLayering G) _).garden
  rw [nativeCoupleLayered_garden]
  exact decodedCouple_decodes _

/-- The native exceptional tree of a state decodes its code. -/
theorem zp_tree_decodes (G : FamilyReconstruction w ι) (i : ι) :
    (G.data.tree (G.family.placement i).lower).DecodesTree (sigStar G i).2.2.garden :=
  decodedTree_decodes _ _

/-- **A coherent carrier-side couple makes the native exceptional couple coherent.** -/
theorem coupleIncoh_eq_zero_of_zp {p q q' : ℕ} {G : FamilyReconstruction w ι} {i : ι}
    (hc : IsCoherentCoupleAt p q q' (zpCodeC G i) (zpObjC G i)) :
    Flower.V5W.coupleIncoh G.data G.plain (stateLayer G) (stateLayer_isLayering G)
      (pairOfLeaf G.skeleton G.plain (G.family.placement i).retained) = 0 := by
  classical
  show (sigStar G i).2.1.incoherency (zpData G i).1.links = 0
  by_cases hν : nuOf G i = -1
  · have hC : zpCodeC G i = (zpData G i).1 := by simp [zpCodeC, hν]
    have hO : zpObjC G i = (sigStar G i).2.1 := by simp [zpObjC, hν]
    rw [hC, hO] at hc
    exact incoherency_eq_zero_of_isCoherentCoupleAt hc
  · have hC : zpCodeC G i = conjCpl (zpData G i).1 := by simp [zpCodeC, hν]
    have hO : zpObjC G i = conjLayered (sigStar G i).2.1 (Equiv.swap (0 : Fin 2) 1) := by simp [zpObjC, hν]
    rw [hC, hO] at hc
    exact incoherency_eq_zero_of_isCoherentCoupleAt_conj (zp_couple_decodes G i) hc

/-- **A coherent carrier-side tree makes the native exceptional tree coherent.** -/
theorem treeIncoh_eq_zero_of_zp {p q q' : ℕ} {G : FamilyReconstruction w ι} {i : ι}
    (hc : IsCoherentTreeAt p q q' (zpCodeT G i) (zpObjT G i)) :
    Flower.V5W.treeIncoh G.data G.plain (stateLayer G) (stateLayer_isLayering G) (G.family.placement i).lower = 0 := by
  classical
  show (sigStar G i).2.2.incoherency ((zpData G i).2.1.treeLinks ((sigStar G i).2.2.garden.sig 0)) = 0
  by_cases hν : nuOf G i = -1
  · have hC : zpCodeT G i = conjChain (zpData G i).2.1 := by simp [zpCodeT, hν]
    have hO : zpObjT G i = conjLayered (sigStar G i).2.2 (Equiv.refl (Fin 1)) := by simp [zpObjT, hν]
    rw [hC, hO] at hc
    exact incoherency_eq_zero_of_isCoherentTreeAt_conj (zp_tree_decodes G i) hc
  · have hC : zpCodeT G i = (zpData G i).2.1 := by simp [zpCodeT, hν]
    have hO : zpObjT G i = (sigStar G i).2.2 := by simp [zpObjT, hν]
    rw [hC, hO] at hc
    exact incoherency_eq_zero_of_isCoherentTreeAt hc

/-- **The selected exceptional couple row of a coherent state is plain.** -/
theorem rowQ_eq_of_zp {p q q' d : ℕ} (κ : KPar d) {G : FamilyReconstruction w ι} {i : ι}
    (hc : IsCoherentCoupleAt p q q' (zpCodeC G i) (zpObjC G i)) :
    rowQ κ G i = KQstar κ.L κ.γ κ.δ κ.F (sigStar G i).2.1 := by
  funext t s k
  exact KQsel_of_incoh_eq_zero (coupleIncoh_eq_zero_of_zp hc) _ _ _ _ _ _ _ _ _ _

/-- **The selected exceptional tree row of a coherent state is plain.** -/
theorem rowT_eq_of_zp {p q q' d : ℕ} (κ : KPar d) {G : FamilyReconstruction w ι} {i : ι}
    (hc : IsCoherentTreeAt p q q' (zpCodeT G i) (zpObjT G i)) :
    rowT κ G i = KTstar κ.L κ.γ κ.δ κ.F (sigStar G i).2.2 := by
  funext t s k
  exact KTsel_of_incoh_eq_zero (treeIncoh_eq_zero_of_zp hc) _ _ _ _ _ _ _ _ _

section Zp
variable {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
  {A : FamilyReconstruction w ι} {sp0 : SplitAt A.skeleton A.family pstar J} {hA : IsPrimeGarden A.skeleton}

/-- The exceptional couple row of every state of `Zp(A)` is plain (`ZpSurj.coherent`). -/
theorem rowQ_zp {d : ℕ} (hZ : ZpSurj p kind pstar J A sp0 hA) (κ : KPar d) {b : ST w ι pstar J}
    (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    rowQ κ b.1 pstar = KQstar κ.L κ.γ κ.δ κ.F (sigStar b.1 pstar).2.1 :=
  rowQ_eq_of_zp κ (hZ.coherent b hb).1

/-- The exceptional tree row of every state of `Zp(A)` is plain (`ZpSurj.coherent`). -/
theorem rowT_zp {d : ℕ} (hZ : ZpSurj p kind pstar J A sp0 hA) (κ : KPar d) {b : ST w ι pstar J}
    (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    rowT κ b.1 pstar = KTstar κ.L κ.γ κ.δ κ.F (sigStar b.1 pstar).2.2 :=
  rowT_eq_of_zp κ (hZ.coherent b hb).2

end Zp

end WaveTurbulence.VineEst
