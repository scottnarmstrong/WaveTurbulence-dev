/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.GraftOutsidePairs

/-! # Finite-list commutation of source A/B steps with a whole-couple graft -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The raw graft list in literal mapped canonical coordinates. -/
theorem graftCouple_framed_pairs_perm (Q C : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2) :
    (graftCouple Q x y C).raw.2.Perm (Q.raw.2.erase (x,y) ++
      C.raw.2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2))) := by
  rw [← pairsAt_frameAddress]
  exact graftCouple_pairs_perm Q x y C hxy

/-- Applying an injective address map to both coordinates preserves injectivity. -/
theorem pairMap_injective {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (fun p : α × α => (f p.1,f p.2)) := by
  intro p q h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  exact Prod.ext (hf h0) (hf h1)

/-- The source A list after framing is exactly the framed local A list plus unchanged outside pairs. -/
theorem graft_opA_pair_formula (Q C : RegCpl) (x y u v : Fin 2 × Path) (c : MiniCplCode)
    (hxy : (x,y) ∈ Q.raw.2) :
    (Q.raw.2.erase (x,y) ++ C.raw.2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2))).erase
      (frameAddress x y u,frameAddress x y v) ++
        (miniCoupleCode c).pairsAt (frameAddress x y u) (frameAddress x y v) =
      Q.raw.2.erase (x,y) ++ (C.raw.opA u v c).2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2)) := by
  rw [List.erase_append_right _ (framed_pair_not_mem_outside Q x y hxy (u,v))]
  rw [← List.map_erase (pairMap_injective _ (frameAddress_injective x y (decodedPair_roots_incomp Q x y hxy)))]
  rw [couple_pairsAt_map (miniCoupleCode c) (frameAddress x y) (frameAddress_respects x y) u v,
    raw_opA_pair_list,List.map_append]
  exact List.append_assoc _ _ _

/-- The source B list after framing is exactly the framed local B list plus unchanged outside pairs. -/
theorem graft_opB_pair_formula (Q C : RegCpl) (x y a : Fin 2 × Path) (m : MiniTreeCode)
    (hxy : (x,y) ∈ Q.raw.2) :
    (Q.raw.2.erase (x,y) ++ C.raw.2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2))).map
      (fun p => (RawCpl.relocate (frameAddress x y a) m.c m.lone p.1,
        RawCpl.relocate (frameAddress x y a) m.c m.lone p.2)) ++
      (miniChain m).pairsAt (nodeSign ![1,-1] (frameAddress x y a)) (frameAddress x y a) =
    Q.raw.2.erase (x,y) ++ (C.raw.opB a m).2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2)) := by
  have hi := decodedPair_roots_incomp Q x y hxy
  have hsign := rawPair_signs Q (x,y) hxy
  have hmap : (C.raw.2.map (fun p => (frameAddress x y p.1,frameAddress x y p.2))).map
      (fun p => (RawCpl.relocate (frameAddress x y a) m.c m.lone p.1,
        RawCpl.relocate (frameAddress x y a) m.c m.lone p.2)) =
      (C.raw.2.map (fun p => (RawCpl.relocate a m.c m.lone p.1,RawCpl.relocate a m.c m.lone p.2))).map
        (fun p => (frameAddress x y p.1,frameAddress x y p.2)) := by
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro p _
    exact Prod.ext (relocate_frameAddress x y a p.1 hi m.c m.lone)
      (relocate_frameAddress x y a p.2 hi m.c m.lone)
  have hnew : (miniChain m).pairsAt (nodeSign ![1,-1] (frameAddress x y a)) (frameAddress x y a) =
      ((miniChain m).pairsAt (nodeSign ![1,-1] a) a).map
        (fun p => (frameAddress x y p.1,frameAddress x y p.2)) := by
    rw [nodeSign_frameAddress ![1,-1] x y a hsign.1 hsign.2]
    exact chain_pairsAt_map (miniChain m) _ (frameAddress_respects x y) _ a
  rw [List.map_append,relocate_outside_pairs_fixed Q x y a hxy,hmap,hnew,raw_opB_pairs,List.map_append]
  exact List.append_assoc _ _ _

end WaveTurbulence.Reg
