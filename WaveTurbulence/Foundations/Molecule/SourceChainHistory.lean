/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SourceChainPositions

/-! # Bare chain codes are exactly actual branching-or-lone B histories -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Every actual source chain history gives a bare code with the exact lone path and raw representation. -/
theorem RawChainHistory.exists_bare_rep {ζ : ℤˣ} {R : RawCpl} {lp : Path} (h : RawChainHistory ζ R lp) :
    ∃ X : RegChain, BareChain X ∧ X.lonePath = lp ∧ RawRep (treeAuxCode X ζ) R := by
  induction h with
  | triv =>
    refine ⟨.nil,trivial,rfl,?_⟩
    have he : treeAuxCode .nil ζ = .triv := by
      by_cases hζ : ζ = 1 <;> simp [treeAuxCode,hζ,joinChains,RegChain.isNil]
    rw [he]
    exact rawRep_triv
  | @opB R lp a m hhist hside hbranch hnode ih =>
    obtain ⟨X,hX,hLp,hrep⟩ := ih
    have hown : R.tree (chainSide ζ) = X.plug ζ .leaf := by rw [hrep.forest,treeAuxCode_own_tree]
    have hnX := hnode
    rw [hside,hown] at hnX
    have hallowed : a.2 ∈ (X.plug ζ .leaf).branching ∨ a.2 = X.lonePath := by
      rw [hown,← hLp] at hbranch
      exact hbranch
    have hA : (chainSide ζ,a.2) = a := Prod.ext hside.symm rfl
    have ht : a ∈ chainNodes X ζ (chainSide ζ,[]) ∨ a = addrExt (chainSide ζ,[]) X.lonePath := by
      have hh := chain_position_of_tree_node X ζ (chainSide ζ) a.2 hnX
      rw [hA] at hh
      exact hh
    have hspine : Below a (addrExt (chainSide ζ,[]) X.lonePath) := by
      have hh := bareChain_permitted_spine X hX ζ (chainSide ζ) a.2 hallowed
      rw [hA] at hh
      exact hh
    let Y := insertChainMini X ζ (chainSide ζ,[]) a m
    have hY := insertChainMini_bare X hX ζ (chainSide ζ,[]) a m ht hspine
    have hcarrier := operationB_treeAux_carrier X ζ a m ht
    have hnewrep : RawRep (treeAuxCode Y ζ) (R.opB a m) := (rawRep_opB hrep a m hnode).recoded hcarrier
    have hhole := (insertChainMini_pairs X ![1,-1] ζ (chainSide ζ,[]) a m (nodeSign_chainSide ζ) ht).2
    have hpath := congrArg (fun z : Fin 2 × Path => z.2) hhole
    change Y.lonePath = (RawCpl.relocate a m.c m.lone (chainSide ζ,X.lonePath)).2 at hpath
    rw [hLp] at hpath
    exact ⟨Y,hY,hpath,hnewrep⟩

/-- Every bare legal-chain code is built by actual B at branching nodes or the actual lone leaf. -/
theorem bareChain_exists_rawHistory (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) :
    ∃ R : RawCpl, RawChainHistory ζ R X.lonePath ∧ RawRep (treeAuxCode X ζ) R := by
  generalize hsize : X.size = N
  induction N using Nat.strong_induction_on generalizing X with
  | h N ih =>
    by_cases hnil : X = .nil
    · subst X
      refine ⟨((.leaf,.leaf),[((0,[]),(1,[]))]),.triv,?_⟩
      have he : treeAuxCode .nil ζ = .triv := by
        by_cases hζ : ζ = 1 <;> simp [treeAuxCode,hζ,joinChains,RegChain.isNil]
      rw [he]
      exact rawRep_triv
    · obtain ⟨Y,m,target,hY,hSY,ht,he⟩ := bareChain_prune X hX hnil ζ (chainSide ζ,[])
      obtain ⟨R,hRY,hrep⟩ := ih Y.size (by omega) Y hY rfl
      have hnodeAux := treeAuxCode_position_node Y ζ target ht
      have hnodeR : target.2 ∈ (R.tree target.1).nodes := by
        rw [hrep.forest]
        exact (coupleForest_node_iff _ target).mpr hnodeAux
      have hside : target.1 = chainSide ζ := (chain_position_below Y ζ (chainSide ζ,[]) target ht).1
      have hown : R.tree (chainSide ζ) = Y.plug ζ .leaf := by rw [hrep.forest,treeAuxCode_own_tree]
      have hnodeY := hnodeR
      rw [hside,hown] at hnodeY
      have habove := bareChain_prune_above_lone X Y hX hY ζ target m hSY ht he
      have hallowed : target.2 ∈ (R.tree (chainSide ζ)).branching ∨ target.2 = Y.lonePath := by
        rw [hown]
        exact chain_node_on_spine_permitted Y ζ target.2 hnodeY habove.2
      have hhistory := RawChainHistory.opB m hRY hside hallowed hnodeR
      have hhole := (insertChainMini_pairs Y ![1,-1] ζ (chainSide ζ,[]) target m (nodeSign_chainSide ζ) ht).2
      rw [he] at hhole
      have hpath := congrArg (fun z : Fin 2 × Path => z.2) hhole
      change X.lonePath = (RawCpl.relocate target m.c m.lone (chainSide ζ,Y.lonePath)).2 at hpath
      rw [← hpath] at hhistory
      have hcarrier := operationB_treeAux_carrier Y ζ target m ht
      change decodedCouple (operationB (treeAuxCode Y ζ) target m) = decodedCouple (treeAuxCode (insertChainMini Y ζ (chainSide ζ,[]) target m) ζ) at hcarrier
      rw [he] at hcarrier
      exact ⟨R.opB target m,hhistory,(rawRep_opB hrep target m hnodeR).recoded hcarrier⟩

/-- DH21 Definition 4.6 and Proposition 4.7: exact construction/code correspondence. -/
theorem rawChainHistory_iff_bare_rep (ζ : ℤˣ) (R : RawCpl) (lp : Path) :
    (∃ S : RawCpl, RawChainHistory ζ S lp ∧ S.1 = R.1 ∧ S.2.Perm R.2) ↔
      ∃ X : RegChain, BareChain X ∧ X.lonePath = lp ∧ RawRep (treeAuxCode X ζ) R := by
  constructor
  · rintro ⟨S,hS,ht,hp⟩
    obtain ⟨X,hX,hLp,hrep⟩ := hS.exists_bare_rep
    exact ⟨X,hX,hLp,ht ▸ hrep.1,hp.symm.trans hrep.2⟩
  · rintro ⟨X,hX,hLp,hrep⟩
    obtain ⟨S,hS,hrepS⟩ := bareChain_exists_rawHistory X hX ζ
    rw [hLp] at hS
    exact ⟨S,hS,hrepS.1.trans hrep.1.symm,hrepS.2.trans hrep.2.symm⟩

end WaveTurbulence.Reg
