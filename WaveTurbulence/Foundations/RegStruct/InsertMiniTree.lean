/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-! # Operation B on intermediate structure data (DH21 Proposition 4.8, cases 2–4)

A code root is handled before its contents. In a chain, the first root and the
second root of the outer pair are handled separately; the lone slot belongs
to the terminal couple, not to an empty chain. Non-node addresses are unchanged.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- One mini-tree viewed as a one-pair regular chain context. -/
def miniChain (m : MiniTreeCode) : RegChain := .pair m .triv .triv .nil .nil

mutual
/-- Insert the specified mini-tree at a node of a decoded couple's two trees. -/
def insertMiniCouple {w : ℕ} (Q : RegCpl) (a b target : Fin w × Path) (m : MiniTreeCode) : RegCpl :=
  if target = a then .type2 (miniChain m) .nil Q
  else if target = b then .type2 .nil (miniChain m) Q
  else match Q with
  | .triv => .triv
  | .type1 c r g d =>
    .type1 c
      (insertMiniCouple r (addrExt a [0]) (addrExt b [c.partner 0]) target m)
      (insertMiniCouple g (addrExt b [1]) (addrExt a [1]) target m)
      (insertMiniCouple d (addrExt a [2]) (addrExt b [c.partner 2]) target m)
  | .type2 p n q =>
    .type2 (insertMiniChain p 1 a target m) (insertMiniChain n (-1) b target m)
      (insertMiniCouple q (addrExt a p.lonePath) (addrExt b n.lonePath) target m)

/-- Insert at one of a chain's represented nodes; its terminal hole is excluded. -/
def insertMiniChain {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) → (Fin w × Path) → MiniTreeCode → RegChain
  | .nil, _, _, _, _ => .nil
  | X@(.pair k r g i s), ζ, a, target, m =>
    if target = a then .pair m .triv .triv .nil X
    else if target = addrExt a ([k.c] ++ i.lonePath) then
      .pair k r g (appendChain i (miniChain m)) s
    else
      .pair k
        (if slotSign ζ k.red.1 = 1 then
          insertMiniCouple r (addrExt a [k.red.1])
            (addrExt a ([k.c] ++ i.lonePath ++ [k.red.2])) target m
        else insertMiniCouple r (addrExt a ([k.c] ++ i.lonePath ++ [k.red.2]))
          (addrExt a [k.red.1]) target m)
        (if slotSign ζ k.green.1 = 1 then
          insertMiniCouple g (addrExt a [k.green.1])
            (addrExt a ([k.c] ++ i.lonePath ++ [k.green.2])) target m
        else insertMiniCouple g (addrExt a ([k.c] ++ i.lonePath ++ [k.green.2]))
          (addrExt a [k.green.1]) target m)
        (insertMiniChain i (slotSign ζ k.c) (addrExt a [k.c]) target m)
        (insertMiniChain s (slotSign (slotSign ζ k.c) k.lone)
          (addrExt a ([k.c] ++ i.lonePath ++ [k.lone])) target m)
end

/-- At the positive root, operation B wraps the whole current couple. -/
theorem insertMiniCouple_at_left {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) (m : MiniTreeCode) :
    insertMiniCouple Q a b a m = .type2 (miniChain m) .nil Q := by
  rw [insertMiniCouple.eq_def,ite_eq_left rfl]

/-- At the distinct negative root, operation B wraps its own tree. -/
theorem insertMiniCouple_at_right {w : ℕ} (Q : RegCpl) (a b : Fin w × Path)
    (hab : b ≠ a) (m : MiniTreeCode) :
    insertMiniCouple Q a b b m = .type2 .nil (miniChain m) Q := by
  rw [insertMiniCouple.eq_def,ite_eq_right hab,ite_eq_left rfl]

/-- At a represented chain root, operation B inserts an adjacent pair before the old spine. -/
theorem insertMiniChain_at_root {w : ℕ} (k m : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a : Fin w × Path) :
    insertMiniChain (.pair k r g i s) ζ a a m = .pair m .triv .triv .nil (.pair k r g i s) := by
  rw [insertMiniChain,ite_eq_left rfl]

end WaveTurbulence.Reg
