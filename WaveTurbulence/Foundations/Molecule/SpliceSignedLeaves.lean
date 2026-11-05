/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceLeafTransport
import Mathlib.Tactic

/-! # Signs under the concrete CL leaf transport
TARGET `block_clcn` (2): matching signs at the three attachment roots
preserves every surviving leaf sign, not just the total signature.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

theorem spliceLeafEquiv_piece (p : SpliceLeafPiece B) :
    (spliceLeafEquiv B (splicePieceNew B p)).1 = splicePieceOld B p := by
  let e := Equiv.ofBijective (splicePieceNew B)
    ⟨splicePieceNew_injective B,splicePieceNew_surjective B⟩
  have h : e.symm (splicePieceNew B p) = p := e.symm_apply_apply p
  change splicePieceOld B (e.symm (splicePieceNew B p)) = splicePieceOld B p
  exact congrArg (splicePieceOld B) h

theorem splicePiece_sign
    (hs : ∀ i, G.sign (B.node i) = G.sign (a.child i)) (p : SpliceLeafPiece B) :
    nodeSign G.sig (splicePieceNew B p).1 = nodeSign G.sig (splicePieceOld B p).1 := by
  cases p with
  | inl l => rfl
  | inr p =>
    obtain ⟨i,q⟩ := p
    have h := hs i
    change nodeSign G.sig (a.1.1,a.1.2++i::q.1) =
      nodeSign G.sig ((B.node i).1.1,(B.node i).1.2++q.1)
    have hnew : nodeSign G.sig (a.1.1,a.1.2++i::q.1) = pathSign (G.sign (a.child i)) q.1 := by
      change pathSign (G.sig a.1.1) (a.1.2++i::q.1) =
        pathSign (pathSign (G.sig a.1.1) (a.1.2++[i])) q.1
      simpa only [List.append_assoc,List.singleton_append] using
        Comb.pathSign_append (G.sig a.1.1) (a.1.2++[i]) q.1
    have hold : nodeSign G.sig ((B.node i).1.1,(B.node i).1.2++q.1) =
        pathSign (G.sign (B.node i)) q.1 := by
      simp only [nodeSign,pathSign,Garden.sign,List.count_append,pow_add,mul_assoc]
    rw [hnew,hold,h]

/-- Every leaf's sign is preserved by the constructed bijection. -/
theorem spliceLeafEquiv_sign
    (hs : ∀ i, G.sign (B.node i) = G.sign (a.child i))
    (l : GLeaf (spliceForest G a B.node)) :
    nodeSign G.sig l.1 = nodeSign G.sig (spliceLeafEquiv B l).1.1 := by
  obtain ⟨p,rfl⟩ := splicePieceNew_surjective B l
  rw [spliceLeafEquiv_piece]
  exact splicePiece_sign B hs p

end WaveTurbulence.Mole
