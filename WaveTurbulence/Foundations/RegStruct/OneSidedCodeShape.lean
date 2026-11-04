/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.TreeDecodingAuxiliary

/-! # A well-formed auxiliary couple with one trivial tree is a single chain -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A terminal non-type-2 code with trivial negative tree is trivial. -/
theorem terminal_eq_triv_of_right_leaf (C : RegCpl) (ht : C.isType2 = false) (hf : C.trees.2 = .leaf) :
    C = .triv := by
  cases C with
  | triv => rfl
  | type1 c r g d => fin_cases c <;> simp [RegCpl.trees] at hf
  | type2 p n q => simp [RegCpl.isType2] at ht

/-- The positive-tree version of the terminal criterion. -/
theorem terminal_eq_triv_of_left_leaf (C : RegCpl) (ht : C.isType2 = false) (hf : C.trees.1 = .leaf) :
    C = .triv := by
  cases C with
  | triv => rfl
  | type1 c r g d => simp [RegCpl.trees] at hf
  | type2 p n q => simp [RegCpl.isType2] at ht

/-- A well-formed code with trivial negative tree has exactly one positive chain. -/
theorem wf_right_leaf_chain (C : RegCpl) (hw : C.wf = true) (hf : C.trees.2 = .leaf) :
    ∃ X : RegChain, X.wf = true ∧ C = treeAuxCode X 1 := by
  cases C with
  | triv => exact ⟨.nil,rfl,rfl⟩
  | type1 c r g d => fin_cases c <;> simp [RegCpl.trees] at hf
  | type2 p n q =>
    simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hw
    have ho := congrArg TTree.order hf
    change (n.plug (-1) q.trees.2).order = 0 at ho
    rw [code_plug_order] at ho
    have hn : n = .nil := eq_nil_of_size_zero n (by omega)
    subst n
    change q.trees.2 = .leaf at hf
    have hq := terminal_eq_triv_of_right_leaf q hw.1.2 hf
    subst q
    refine ⟨p,hw.1.1.1.1,?_⟩
    rw [treeAuxCode,ite_eq_left rfl,joinChains,ite_eq_right (by rw [hw.2]; decide)]

/-- A well-formed code with trivial positive tree has exactly one negative chain. -/
theorem wf_left_leaf_chain (C : RegCpl) (hw : C.wf = true) (hf : C.trees.1 = .leaf) :
    ∃ X : RegChain, X.wf = true ∧ C = treeAuxCode X (-1) := by
  cases C with
  | triv => exact ⟨.nil,rfl,rfl⟩
  | type1 c r g d => simp [RegCpl.trees] at hf
  | type2 p n q =>
    simp only [RegCpl.wf,Bool.and_eq_true,Bool.not_eq_true'] at hw
    have ho := congrArg TTree.order hf
    change (p.plug 1 q.trees.1).order = 0 at ho
    rw [code_plug_order] at ho
    have hp : p = .nil := eq_nil_of_size_zero p (by omega)
    subst p
    change q.trees.1 = .leaf at hf
    have hq := terminal_eq_triv_of_left_leaf q hw.1.2 hf
    subst q
    refine ⟨n,hw.1.1.1.2,?_⟩
    rw [treeAuxCode,ite_eq_right (by decide)]
    rw [joinChains,ite_eq_right (by rw [hw.2]; decide)]

/-- An actual tree-to-couple matching fixes which of the two single-chain forms is present. -/
theorem wf_matchingTree_aux_shape (C : RegCpl) (G : Garden 1) (hw : C.wf = true)
    (hM : G.MatchesTreeCouple C.raw) : ∃ X : RegChain, X.wf = true ∧ C = treeAuxCode X (G.sig 0) := by
  by_cases hζ : G.sig 0 = 1
  · have hf := hM.2.1
    change C.raw.tree (1 - if G.sig 0 = 1 then 0 else 1) = .leaf at hf
    simp only [hζ,ite_true] at hf
    obtain ⟨X,hX,he⟩ := wf_right_leaf_chain C hw hf
    exact ⟨X,hX,by simpa only [hζ] using he⟩
  · have hm : G.sig 0 = -1 := (Int.units_eq_one_or _).resolve_left hζ
    have hf := hM.2.1
    change C.raw.tree (1 - if G.sig 0 = 1 then 0 else 1) = .leaf at hf
    simp only [hζ,ite_false] at hf
    obtain ⟨X,hX,he⟩ := wf_left_leaf_chain C hw hf
    exact ⟨X,hX,by simpa only [hm] using he⟩

end WaveTurbulence.Reg
