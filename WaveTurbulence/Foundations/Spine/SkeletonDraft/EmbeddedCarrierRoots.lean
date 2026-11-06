/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedCouple
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.EmbeddedPairedTree

/-! # Actual embedded carriers depend only on the ambient garden and ordered boundaries -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem subCoupleGarden_eq_of_roots {w : ℕ} {G : Garden w} {a b c d : GNode G.tree}
    (h : Comb.IsSubCouple G a b) (k : Comb.IsSubCouple G c d) (ha : a = c) (hb : b = d) :
    Comb.subCoupleGarden h = Comb.subCoupleGarden k := by
  cases ha
  cases hb
  rfl

theorem embeddedPairedTree_eq_of_roots {w : ℕ} {G : Garden w} {a b c d : GNode G.tree}
    (h : Comb.IsSubPairedTree G a b) (k : Comb.IsSubPairedTree G c d) (ha : a = c) (hb : b = d) :
    Comb.embeddedPairedTree h = Comb.embeddedPairedTree k := by
  cases ha
  cases hb
  rfl

end WaveTurbulence.Reg.Skeleton
