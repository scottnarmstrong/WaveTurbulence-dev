/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Final2

/-! # ZP-SURJ: orders, signs and counts of the carrier-side objects -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

theorem conjLayered_order (L : LayeredGarden 1) : (conjLayered L (Equiv.refl (Fin 1))).garden.order = L.garden.order := rfl

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι}
variable (A : FamilyReconstruction w ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

omit hcan hel htc hcc in
theorem two_zpN : 2 * zpN A pstar = (A.data.tree (A.family.placement pstar).lower).size +
    (A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).size := by
  have h1 : (sigStar A pstar).2.1.garden.order = (A.data.couple (pairOfLeaf A.skeleton A.plain
      (A.family.placement pstar).retained)).size := by
    change (nativeCoupleLayered _ _ _ _ _).garden.order = _
    rw [nativeCoupleLayered_garden]; exact decodedCouple_order _
  have h2 : (sigStar A pstar).2.2.garden.order = (A.data.tree (A.family.placement pstar).lower).size := by
    change (decodedTree _ _).order = _
    exact decodedTree_order _ _
  have he : Even ((A.data.tree (A.family.placement pstar).lower).size +
      (A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).size) :=
    (regChain_size_even _).add (regCpl_size_even _)
  unfold zpN
  rw [h1, h2, add_comm]
  exact Nat.two_mul_div_two_of_even he

include hcan hel htc hcc

theorem order_con {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε) :
    (conLQ con).garden.order + (conLX con).garden.order = 2 * zpN A pstar := by
  rw [two_zpN]
  have hq : (conLQ con).garden = decodedCouple con.newCouple := decodedCouple_unique _ _ (conLQ_decodes con)
  have ht : (conLX con).garden = decodedTree con.newTree (srcSign (A.source pstar hcan hel htc hcc) ε) :=
    decodedTree_unique _ _ _ (conLX_decodes con) (conLX_sig con)
  rw [hq, ht, decodedCouple_order, decodedTree_order, add_comm]
  exact con.combinedOrder

open Classical in
theorem carrierOf_IIb {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (hv : nuOf (opOut A pstar hcan hel htc hcc con) pstar = -1) :
    zpCarrierOf (opOut A pstar hcan hel htc hcc con) pstar =
      (con.newCouple, conjChain con.newTree, conLQ con, conjLayered (conLX con) (Equiv.refl (Fin 1))) := by
  have hd := zpData_op A hcan hel htc hcc con
  have hs := sigStar_op A pstar hcan hel htc hcc con
  unfold zpCarrierOf zpCodeC zpCodeT zpObjC zpObjT
  rw [if_pos hv, if_pos hv, if_pos hv, if_pos hv, hd, hs]

theorem carrier_of_IIb {ε : Bool} (con : LFConstruction (A.source pstar hcan hel htc hcc) ε)
    (hv : nuOf (opOut A pstar hcan hel htc hcc con) pstar = -1) (hn : NR A hcan hel htc hcc con) :
    ZpCarrier p A pstar (zpCarrierOf (opOut A pstar hcan hel htc hcc con) pstar) := by
  rw [carrierOf_IIb A hcan hel htc hcc con hv]
  obtain ⟨c1, c2⟩ := carrier_coherent A hcan hel htc hcc con hv hn
  have hν : srcSign (A.source pstar hcan hel htc hcc) ε = -1 := by
    rw [← nuOf_op A hcan hel htc hcc con]; exact hv
  refine ⟨c1, c2, ?_, ?_, ?_⟩
  · show -(conLX con).garden.sig 0 = 1
    rw [conLX_sig con, hν]; decide
  · show (conLQ con).garden.order + (conLX con).garden.order = _
    exact order_con A hcan hel htc hcc con
  · show topBranchCount (conLQ con) p + topBranchCount (conjLayered (conLX con) (Equiv.refl (Fin 1))) p =
      topBranchCount (sigStar A pstar).2.1 p + topBranchCount (sigStar A pstar).2.2 p
    rw [topBranchCount_conj (conjLayered_isConjugateBy (conLX con) (Equiv.refl (Fin 1)))]
    have h1 := srcRaw_eq_con A hcan hel htc hcc con
    have h2 := srcRaw_eq_start (p := p) (pstar := pstar) A
    omega

end WaveTurbulence.ZpSurj
