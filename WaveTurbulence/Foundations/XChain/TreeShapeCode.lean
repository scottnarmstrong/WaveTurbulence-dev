/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeLeafCard
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! A linear-length prefix code for ternary top trees gives an exponential shape count. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def treeShapeCode : TTree → List Bool
  | .leaf => [false]
  | .node l m r => true :: (treeShapeCode l ++ treeShapeCode m ++ treeShapeCode r)

def parseTreeShape : ℕ → List Bool → Option (TTree × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: s => some (.leaf, s)
  | n + 1, true :: s => do
    let (l, s₁) ← parseTreeShape n s
    let (m, s₂) ← parseTreeShape n s₁
    let (r, s₃) ← parseTreeShape n s₂
    pure (.node l m r, s₃)

theorem parseTreeShape_code (fuel : ℕ) (T : TTree) (h : T.order < fuel) (s : List Bool) :
    parseTreeShape fuel (treeShapeCode T ++ s) = some (T, s) := by
  induction fuel generalizing T s with
  | zero => omega
  | succ n ih =>
    cases T with
    | leaf => rfl
    | node l m r =>
      have hl : l.order < n := by simp only [TTree.order] at h; omega
      have hm : m.order < n := by simp only [TTree.order] at h; omega
      have hr : r.order < n := by simp only [TTree.order] at h; omega
      simp [treeShapeCode, List.append_assoc, parseTreeShape, ih l hl, ih m hm, ih r hr]

theorem treeShapeCode_injective : Function.Injective treeShapeCode := by
  intro T S h
  let fuel := T.order + S.order + 1
  have ht := parseTreeShape_code fuel T (by dsimp [fuel]; omega) []
  have hs := parseTreeShape_code fuel S (by dsimp [fuel]; omega) []
  rw [h, hs] at ht
  exact (congrArg Prod.fst (Option.some.inj ht)).symm

theorem treeShapeCode_length (T : TTree) : (treeShapeCode T).length = 3 * T.order + 1 := by
  induction T with
  | leaf => rfl
  | node l m r hl hm hr =>
    simp only [treeShapeCode, List.length_cons, List.length_append, hl, hm, hr, TTree.order]
    omega

noncomputable def boundedTreeShapeCode (N : ℕ) (T : {T : TTree // T.order ≤ N}) :
    Fin (3 * N + 1) → Option Bool := fun i => (treeShapeCode T.1)[i.1]?

theorem boundedTreeShapeCode_injective (N : ℕ) : Function.Injective (boundedTreeShapeCode N) := by
  intro T S h
  apply Subtype.ext
  apply treeShapeCode_injective
  apply List.ext_getElem?'
  intro i hi
  have hlenT : (treeShapeCode T.1).length ≤ 3 * N + 1 := by rw [treeShapeCode_length]; omega
  have hlenS : (treeShapeCode S.1).length ≤ 3 * N + 1 := by rw [treeShapeCode_length]; omega
  have hiN : i < 3 * N + 1 := lt_of_lt_of_le hi (max_le hlenT hlenS)
  exact congrFun h ⟨i, hiN⟩

theorem card_bounded_trees_le (N : ℕ) : Nat.card {T : TTree // T.order ≤ N} ≤ 3 ^ (3 * N + 1) := by
  have h := Nat.card_le_card_of_injective (boundedTreeShapeCode N) (boundedTreeShapeCode_injective N)
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_fin] using h

end WaveTurbulence.Induct
