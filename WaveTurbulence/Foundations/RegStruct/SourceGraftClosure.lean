/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.GraftOperationFidelity

/-! # Actual source regularity is closed under whole-couple leaf-pair grafting

An inserted source history is replayed at the literal framed A/B positions.
Each source step is produced by the original inductive constructors, with its
actual pair/node membership checked. No graft-closure premise is assumed.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Replaying any actual raw source history inside a regular pair slot preserves source regularity. -/
theorem graft_isRegular_of_rawRegular {R : RawCpl} (hR : RawRegular R) :
    ∀ (C : RegCpl), RawRep C R → ∀ (Q : RegCpl), IsRegularCouple (decodedCouple Q) →
      ∀ (x y : Fin 2 × Path), (x,y) ∈ Q.raw.2 → IsRegularCouple (decodedCouple (graftCouple Q x y C)) := by
  induction hR with
  | triv =>
    intro C hC Q hQ x y hxy
    have he := hC.carrier_eq rawRep_triv
    have hg := (graftCouple_carrier_congr Q C .triv x y hxy he).trans (graftCouple_triv_carrier Q x y hxy)
    rw [hg]
    exact hQ
  | @opA R u v c hR huv ih =>
    intro C hC Q hQ x y hxy
    obtain ⟨D,_,hD⟩ := RawRegular.exists_wf_rawRep hR
    have huvD : (u,v) ∈ D.raw.2 := hD.2.mem_iff.mp huv
    have hnew := rawRep_opA hD u v c huv
    have hcarrier : decodedCouple (operationA D u v c) = decodedCouple C := hnew.carrier_eq hC
    have hold : IsRegularCouple (decodedCouple (graftCouple Q x y D)) := ih D hD Q hQ x y hxy
    have hposition := graftCouple_pair_mem Q D x y hxy (u,v) huvD
    have hstep := isRegularCouple_operationA (graftCouple Q x y D) hold
      (frameAddress x y u) (frameAddress x y v) c hposition
    rw [operationA_graft_carrier Q D x y u v c hxy huvD] at hstep
    have hg := graftCouple_carrier_congr Q (operationA D u v c) C x y hxy hcarrier
    rw [← hg]
    exact hstep
  | @opB R a m hR ha ih =>
    intro C hC Q hQ x y hxy
    obtain ⟨D,_,hD⟩ := RawRegular.exists_wf_rawRep hR
    have haD : a ∈ coupleNodes D (0,[]) (1,[]) := by
      apply (coupleForest_node_iff D a).mp
      simpa only [hD.forest] using ha
    have hnew := rawRep_opB hD a m ha
    have hcarrier : decodedCouple (operationB D a m) = decodedCouple C := hnew.carrier_eq hC
    have hold : IsRegularCouple (decodedCouple (graftCouple Q x y D)) := ih D hD Q hQ x y hxy
    have hposition := graftCouple_node_mem Q D x y a hxy haD
    have hstep := isRegularCouple_operationB (graftCouple Q x y D) hold (frameAddress x y a) m hposition
    rw [operationB_graft_carrier Q D x y a m hxy haD] at hstep
    have hg := graftCouple_carrier_congr Q (operationB D a m) C x y hxy hcarrier
    rw [← hg]
    exact hstep

/-- Replacing an actual leaf pair of a source-regular couple by any source-regular couple
again gives an actual source-regular couple. -/
theorem isRegularCouple_graft (Q C : RegCpl) (hQ : IsRegularCouple (decodedCouple Q))
    (hC : IsRegularCouple (decodedCouple C)) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2) :
    IsRegularCouple (decodedCouple (graftCouple Q x y C)) := by
  obtain ⟨R,hR,hrep⟩ := exists_rawRep_of_isRegularCouple C hC
  exact graft_isRegular_of_rawRegular hR C hrep Q hQ x y hxy

end WaveTurbulence.Reg
