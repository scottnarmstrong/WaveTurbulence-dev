/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.Type2Frames

/-! # B insertion in the terminal couple of a two-chain context -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Terminal-couple insertion leaves both surrounding chain codes untouched. -/
theorem insertMiniCouple_type2_terminal (p n : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b)
    (ht : target ∈ coupleNodes q (addrExt a p.lonePath) (addrExt b n.lonePath)) :
    insertMiniCouple (.type2 p n q) a b target m =
      .type2 p n (insertMiniCouple q (addrExt a p.lonePath) (addrExt b n.lonePath) target m) := by
  have hp := terminal_node_not_in_chain p q 1 a (addrExt b n.lonePath) target
    (hab.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  have hn := terminal_node_not_in_chain_swap n q (-1) b (addrExt a p.lonePath) target
    (hab.symm.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [insertMiniChain_outside p _ _ target m hp,insertMiniChain_outside n _ _ target m hn]

/-- Lift an arbitrary terminal-couple replacement permutation through both chains. -/
theorem type2_terminal_constructor_perm (p n : RegChain) (q q' : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode)
    (N : List ((Fin 2 × Path) × (Fin 2 × Path))) (hab : IncompAddr a b)
    (ht : target ∈ coupleNodes q (addrExt a p.lonePath) (addrExt b n.lonePath))
    (hlocal : (q'.pairsAt (addrExt a p.lonePath) (addrExt b n.lonePath)).Perm
      ((q.pairsAt (addrExt a p.lonePath) (addrExt b n.lonePath)).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N)) :
    ((RegCpl.type2 p n q').pairsAt a b).Perm
      (((RegCpl.type2 p n q).pairsAt a b).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N) := by
  have hp := terminal_node_chain_pairs_fixed p q 1 a (addrExt b n.lonePath) target m
    (hab.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  have hn := terminal_node_chain_pairs_fixed_swap n q (-1) b (addrExt a p.lonePath) target m
    (hab.symm.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  simp only [RegCpl.pairsAt,List.map_append]
  rw [hp,hn]
  exact perm_lift_last _ _ _ _ N hlocal

/-- A positive-chain insertion changes only that chain's code. -/
theorem insertMiniCouple_type2_positive (p n : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b) (ht : target ∈ chainNodes p 1 a) :
    insertMiniCouple (.type2 p n q) a b target m =
      .type2 (insertMiniChain p 1 a target m) n q := by
  have hsep := hab.descendants (chainNodes_below p 1 a target ht) ⟨rfl,List.prefix_refl _⟩
  have hq := chain_node_not_in_terminal p q 1 a (addrExt b n.lonePath) target
    (hab.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [insertMiniChain_of_incomparable n _ _ target m hsep,insertMiniCouple_outside q _ _ target m hq]

/-- A negative-chain insertion changes only that chain's code. -/
theorem insertMiniCouple_type2_negative (p n : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : target ≠ a) (hb : target ≠ b) (ht : target ∈ chainNodes n (-1) b) :
    insertMiniCouple (.type2 p n q) a b target m =
      .type2 p (insertMiniChain n (-1) b target m) q := by
  have hsep := hab.symm.descendants (chainNodes_below n (-1) b target ht) ⟨rfl,List.prefix_refl _⟩
  have hq := chain_node_not_in_terminal_swap n q (-1) b (addrExt a p.lonePath) target
    (hab.symm.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ _)) ht
  rw [insertMiniCouple.eq_def,ite_eq_right ha,ite_eq_right hb]
  dsimp only
  rw [insertMiniChain_of_incomparable p _ _ target m hsep,insertMiniCouple_outside q _ _ target m hq]

/-- A chain's moved terminal root transports the unchanged terminal couple. -/
theorem positive_terminal_pairs_transport (p p' n : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes p 1 a)
    (hh : addrExt a p'.lonePath = RawCpl.relocate target m.c m.lone (addrExt a p.lonePath)) :
    q.pairsAt (addrExt a p'.lonePath) (addrExt b n.lonePath) =
      (q.pairsAt (addrExt a p.lonePath) (addrExt b n.lonePath)).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) := by
  have hl := relocate_respectsAt_of_not_below target (addrExt a p.lonePath) m.c m.lone
    (chainNodes_not_below_lone p 1 a target ht)
  have hsep := hab.descendants (chainNodes_below p 1 a target ht) (below_extend b n.lonePath)
  have hr := relocate_respects_incomparable target (addrExt b n.lonePath) m.c m.lone hsep.1 hsep.2
  have he := couple_pairsAt_map_local q (RawCpl.relocate target m.c m.lone) _ _ hl hr
  rw [← hh,relocate_eq_of_not_below _ _ _ _ hsep.1] at he
  exact he

/-- The negative-chain version transports the other root of the terminal couple. -/
theorem negative_terminal_pairs_transport (p n n' : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes n (-1) b)
    (hh : addrExt b n'.lonePath = RawCpl.relocate target m.c m.lone (addrExt b n.lonePath)) :
    q.pairsAt (addrExt a p.lonePath) (addrExt b n'.lonePath) =
      (q.pairsAt (addrExt a p.lonePath) (addrExt b n.lonePath)).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) := by
  have hr := relocate_respectsAt_of_not_below target (addrExt b n.lonePath) m.c m.lone
    (chainNodes_not_below_lone n (-1) b target ht)
  have hsep := hab.symm.descendants (chainNodes_below n (-1) b target ht) (below_extend a p.lonePath)
  have hl := relocate_respects_incomparable target (addrExt a p.lonePath) m.c m.lone hsep.1 hsep.2
  have he := couple_pairsAt_map_local q (RawCpl.relocate target m.c m.lone) _ _ hl hr
  rw [← hh,relocate_eq_of_not_below _ _ _ _ hsep.1] at he
  exact he

/-- Lift an actual positive-chain step's two transport conclusions through a type-2 constructor. -/
theorem type2_positive_constructor_perm (p p' n : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode)
    (N : List ((Fin 2 × Path) × (Fin 2 × Path))) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes p 1 a)
    (hh : addrExt a p'.lonePath = RawCpl.relocate target m.c m.lone (addrExt a p.lonePath))
    (hlocal : (p'.pairsAt 1 a).Perm ((p.pairsAt 1 a).map (fun x =>
      (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N)) :
    ((RegCpl.type2 p' n q).pairsAt a b).Perm
      (((RegCpl.type2 p n q).pairsAt a b).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N) := by
  have hn := relocate_chain_pairs_fixed n (-1) b target m
    (hab.descendants (chainNodes_below p 1 a target ht) ⟨rfl,List.prefix_refl _⟩)
  rw [RegCpl.pairsAt,positive_terminal_pairs_transport p p' n q a b target m hab ht hh,RegCpl.pairsAt]
  simp only [List.map_append]
  rw [hn]
  exact perm_lift_first _ _ _ _ N hlocal

/-- Lift an actual negative-chain step's two transport conclusions through a type-2 constructor. -/
theorem type2_negative_constructor_perm (p n n' : RegChain) (q : RegCpl)
    (a b target : Fin 2 × Path) (m : MiniTreeCode)
    (N : List ((Fin 2 × Path) × (Fin 2 × Path))) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes n (-1) b)
    (hh : addrExt b n'.lonePath = RawCpl.relocate target m.c m.lone (addrExt b n.lonePath))
    (hlocal : (n'.pairsAt (-1) b).Perm ((n.pairsAt (-1) b).map (fun x =>
      (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N)) :
    ((RegCpl.type2 p n' q).pairsAt a b).Perm
      (((RegCpl.type2 p n q).pairsAt a b).map (fun x =>
        (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++ N) := by
  have hp := relocate_chain_pairs_fixed p 1 a target m
    (hab.symm.descendants (chainNodes_below n (-1) b target ht) ⟨rfl,List.prefix_refl _⟩)
  rw [RegCpl.pairsAt,negative_terminal_pairs_transport p n n' q a b target m hab ht hh,RegCpl.pairsAt]
  simp only [List.map_append]
  rw [hp]
  exact perm_lift_middle _ _ _ _ N hlocal

end WaveTurbulence.Reg
