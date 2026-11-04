/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # Orders of regular-object structure codes (DH21 Propositions 4.7–4.8)

Order identities apply to all codes, independently of the uniqueness side conditions.
-/

public section

namespace WaveTurbulence.Reg
open TTree

mutual
/-- Decoding a couple code has exactly the indicated order. -/
theorem code_trees_order (Q : RegCpl) : Q.trees.1.order + Q.trees.2.order = Q.size := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ =>
    have h₁ := code_trees_order Q₁
    have h₂ := code_trees_order Q₂
    have h₃ := code_trees_order Q₃
    fin_cases c <;> simp [RegCpl.trees, TTree.order, RegCpl.size] <;> omega
  | type2 Xp Xm Qlp =>
    have h₀ := code_trees_order Qlp
    rw [RegCpl.trees, code_plug_order, code_plug_order, RegCpl.size]
    omega
termination_by structural Q

/-- Filling a chain's lone slot adds the chain's order to the inserted subtree's order. -/
theorem code_plug_order (X : RegChain) (ζ : ℤˣ) (h : TTree) :
    (X.plug ζ h).order = X.size + h.order := by
  cases X with
  | nil => simp only [RegChain.plug, RegChain.size, Nat.zero_add]
  | pair m Qr Qg inner rest =>
    have hr := code_trees_order Qr
    have hg := code_trees_order Qg
    obtain ⟨c,b⟩ := m
    rcases Int.units_eq_one_or ζ with hz | hz <;> subst ζ
    all_goals
      fin_cases c <;> fin_cases b <;>
        simp [RegChain.plug, node3, MiniTreeCode.lone, MiniTreeCode.red,
          slotSign, treeOfSign, TTree.order, code_plug_order inner, code_plug_order rest,
          RegChain.size] <;> omega
termination_by structural X
end

/-- Draft B2's order characterization, with no unfinished characterization imported. -/
theorem size_eq_order {Q : RegCpl} {G : Garden 2} (h : Q.Decodes G) :
    G.order = Q.size := by
  obtain ⟨_,ht₀,ht₁,_⟩ := h
  simpa only [Garden.order, Fin.sum_univ_two, ht₀, ht₁] using code_trees_order Q

mutual
/-- Every couple code has even order. -/
theorem code_size_even (Q : RegCpl) : Even Q.size := by
  cases Q with
  | triv => exact ⟨0,rfl⟩
  | type1 c a b d =>
    simpa only [RegCpl.size, Nat.add_assoc] using
      ((code_size_even a).add (code_size_even b)).add
        ((code_size_even d).add (by decide : Even 2))
  | type2 a b q => exact ((chain_size_even a).add (chain_size_even b)).add (code_size_even q)
termination_by structural Q

/-- Every chain code (with its inserted couples) has even order. -/
theorem chain_size_even (X : RegChain) : Even X.size := by
  cases X with
  | nil => exact ⟨0,rfl⟩
  | pair m r g i s =>
    simpa only [RegChain.size, Nat.add_assoc] using
      (((code_size_even r).add (code_size_even g)).add (chain_size_even i)).add
        ((chain_size_even s).add (by decide : Even 2))
termination_by structural X
end

end WaveTurbulence.Reg
