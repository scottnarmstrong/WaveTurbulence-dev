/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.GraftOperationPairFormulas

/-! # Replaying an actual source A/B step inside an actual graft -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A local A-step can be replayed at its literal globally framed pair in the graft. -/
theorem operationA_graft_carrier (Q C : RegCpl) (x y u v : Fin 2 × Path) (c : MiniCplCode)
    (hxy : (x,y) ∈ Q.raw.2) (huv : (u,v) ∈ C.raw.2) :
    decodedCouple (operationA (graftCouple Q x y C) (frameAddress x y u) (frameAddress x y v) c) =
      decodedCouple (graftCouple Q x y (operationA C u v c)) := by
  have hposition := graftCouple_pair_mem Q C x y hxy (u,v) huv
  have hsource := operationA_pairs_perm (graftCouple Q x y C) _ _ c hposition
  have hold := graftCouple_framed_pairs_perm Q C x y hxy
  have hraw : ((graftCouple Q x y C).raw.opA (frameAddress x y u) (frameAddress x y v) c).2.Perm
      (Q.raw.2.erase (x,y) ++ (C.raw.opA u v c).2.map
        (fun p => (frameAddress x y p.1,frameAddress x y p.2))) := by
    rw [raw_opA_pair_list]
    have hh := (hold.erase (frameAddress x y u,frameAddress x y v)).append_right
      ((miniCoupleCode c).pairsAt (frameAddress x y u) (frameAddress x y v))
    rw [graft_opA_pair_formula Q C x y u v c hxy] at hh
    exact hh
  have hdesired := (graftCouple_framed_pairs_perm Q (operationA C u v c) x y hxy).trans
    (((operationA_pairs_perm C u v c huv).map (fun p => (frameAddress x y p.1,frameAddress x y p.2))).append_left _)
  exact decodedCouple_eq_of_rawPairs_perm _ _ (hsource.trans (hraw.trans hdesired.symm))

/-- A local B-step can be replayed at its literal globally framed node in the graft. -/
theorem operationB_graft_carrier (Q C : RegCpl) (x y a : Fin 2 × Path) (m : MiniTreeCode)
    (hxy : (x,y) ∈ Q.raw.2) (ha : a ∈ coupleNodes C (0,[]) (1,[])) :
    decodedCouple (operationB (graftCouple Q x y C) (frameAddress x y a) m) =
      decodedCouple (graftCouple Q x y (operationB C a m)) := by
  have hposition := graftCouple_node_mem Q C x y a hxy ha
  have hsource := operationB_pairs_perm (graftCouple Q x y C) _ m hposition
  have hold := graftCouple_framed_pairs_perm Q C x y hxy
  have hraw : ((graftCouple Q x y C).raw.opB (frameAddress x y a) m).2.Perm
      (Q.raw.2.erase (x,y) ++ (C.raw.opB a m).2.map
        (fun p => (frameAddress x y p.1,frameAddress x y p.2))) := by
    rw [raw_opB_pairs]
    have hh := (hold.map (fun p =>
        (RawCpl.relocate (frameAddress x y a) m.c m.lone p.1,
          RawCpl.relocate (frameAddress x y a) m.c m.lone p.2))).append_right
      ((miniChain m).pairsAt (nodeSign ![1,-1] (frameAddress x y a)) (frameAddress x y a))
    rw [graft_opB_pair_formula Q C x y a m hxy] at hh
    exact hh
  have hdesired := (graftCouple_framed_pairs_perm Q (operationB C a m) x y hxy).trans
    (((operationB_pairs_perm C a m ha).map (fun p => (frameAddress x y p.1,frameAddress x y p.2))).append_left _)
  exact decodedCouple_eq_of_rawPairs_perm _ _ (hsource.trans (hraw.trans hdesired.symm))

/-- Replacing an actual leaf pair by the trivial couple preserves its actual carrier. -/
theorem graftCouple_triv_carrier (Q : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2) :
    decodedCouple (graftCouple Q x y .triv) = decodedCouple Q := by
  apply decodedCouple_eq_of_rawPairs_perm
  apply (graftCouple_pairs_perm Q x y .triv hxy).trans
  change (Q.raw.2.erase (x,y) ++ [(x,y)]).Perm Q.raw.2
  apply (List.perm_append_comm : (Q.raw.2.erase (x,y) ++ [(x,y)]).Perm ([(x,y)] ++ Q.raw.2.erase (x,y))).trans
  exact (List.perm_cons_erase hxy).symm

end WaveTurbulence.Reg
