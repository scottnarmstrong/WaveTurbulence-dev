/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeInt

/-!
# The time domain of a tree, as in the source

DH21 (timedom0), DH23 (defdomaine) (L474) and Wave B's `kDomain` state the time domain of a tree
node by node: `0 < t_𝔫`, `t_𝔫 < u`, and `t_{𝔫'} < t_𝔫` for every branching child `𝔫'` of `𝔫`
(`treeDomF`). It is the recursive domain `treeDomR` (`treeDomF_eq`).
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree Set

/-- `q` is a branching child of `p`. -/
def TB.IsChild {T : TTree} (q p : TB T) : Prop := ∃ i : Fin 3, q.1 = p.1 ++ [i]

/-- **The time domain of a tree, node by node** (DH23 (defdomaine)). -/
def treeDomF (T : TTree) (u : ℝ) : Set (TB T → ℝ) :=
  {τ | ∀ p, 0 < τ p ∧ τ p < u ∧ ∀ q : TB T, q.IsChild p → τ q < τ p}

/-- Times decrease along ancestry. -/
theorem le_of_prefix {T : TTree} {τ : TB T → ℝ} (hτ : ∀ p q : TB T, q.IsChild p → τ q < τ p)
    (p : TB T) : ∀ (q : TTree.Path) (hq : p.1 ++ q ∈ T.branching), τ ⟨p.1 ++ q, hq⟩ ≤ τ p := by
  intro q
  induction q using List.reverseRecOn with
  | nil => intro hq; simp
  | append_singleton q i ih =>
    intro hq
    have hq' : p.1 ++ q ∈ T.branching := by
      rw [← List.append_assoc] at hq
      exact mem_branching_of_append _ _ _ hq
    have h1 := hτ ⟨p.1 ++ q, hq'⟩ ⟨p.1 ++ (q ++ [i]), hq⟩ ⟨i, by simp⟩
    exact h1.le.trans (ih hq')

/-- Every prefix of a branching node is a branching node. -/
theorem mem_branching_of_prefix (T : TTree) (p : TTree.Path) :
    ∀ q : TTree.Path, p ++ q ∈ T.branching → p ∈ T.branching := by
  intro q
  induction q using List.reverseRecOn with
  | nil => simp
  | append_singleton q i ih =>
    intro h
    rw [← List.append_assoc] at h
    exact ih (mem_branching_of_append _ _ _ h)

theorem treeDomF_eq : ∀ (T : TTree) (u : ℝ), treeDomF T u = treeDomR T u
  | .leaf, u => by
    ext τ
    simp only [treeDomF, treeDomR, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact fun p => absurd p.2 (not_mem_branching_leaf _)
  | .node l m r, u => by
    ext τ
    rw [treeDomR, Set.mem_ofPred_eq, ← treeDomF_eq l, ← treeDomF_eq m, ← treeDomF_eq r]
    have hroot : tRoot τ = τ (TB.root l m r) := rfl
    constructor
    · intro h
      have hbelow : ∀ (i : Fin 3) (q : TTree.Path) (hq : i :: q ∈ (TTree.node l m r).branching),
          τ ⟨i :: q, hq⟩ < tRoot τ := by
        intro i q hq
        have h0 : [i] ∈ (TTree.node l m r).branching :=
          mem_branching_of_prefix _ [i] q hq
        have h1 := le_of_prefix (fun p q hqp => (h p).2.2 q hqp) ⟨[i], h0⟩ q hq
        have h2 := (h (TB.root l m r)).2.2 ⟨[i], h0⟩ ⟨i, rfl⟩
        exact h1.trans_lt h2
      have hsubt : ∀ i : Fin 3, restrT i τ ∈ treeDomF (tchild (TTree.node l m r) i) (tRoot τ) := by
        intro i q
        refine ⟨(h _).1, hbelow i q.1 _, fun q' ⟨k, hk⟩ => (h _).2.2 _ ⟨k, ?_⟩⟩
        simp [TB.sub, hk]
      exact ⟨(h _).1, (h _).2.1, hsubt 0, hsubt 1, hsubt 2⟩
    · rintro ⟨h0, hu, hl, hm, hr⟩
      have hsubt : ∀ i : Fin 3, restrT i τ ∈ treeDomF (tchild (TTree.node l m r) i) (tRoot τ) := by
        intro i
        fin_cases i
        · exact hl
        · exact hm
        · exact hr
      rintro ⟨_ | ⟨i, p'⟩, hp⟩
      · refine ⟨h0, hu, fun q ⟨k, hk⟩ => ?_⟩
        have hk' : q.1 = k :: [] := by simpa using hk
        have hq0 : ([] : TTree.Path) ∈ (tchild (TTree.node l m r) k).branching :=
          (cons_mem_branching_node l m r k []).1 (hk' ▸ q.2)
        have := (hsubt k ⟨[], hq0⟩).2.1
        have e : q = TB.sub l m r k ⟨[], hq0⟩ := Subtype.ext hk'
        rw [e]
        exact this
      · have hp' : p' ∈ (tchild (TTree.node l m r) i).branching :=
          (cons_mem_branching_node l m r i p').1 hp
        have hh := hsubt i ⟨p', hp'⟩
        refine ⟨hh.1, hh.2.1.trans hu, fun q ⟨k, hk⟩ => ?_⟩
        have hk' : q.1 = i :: (p' ++ [k]) := by simpa using hk
        have hq0 : p' ++ [k] ∈ (tchild (TTree.node l m r) i).branching :=
          (cons_mem_branching_node l m r i _).1 (hk' ▸ q.2)
        have e : q = TB.sub l m r i ⟨p' ++ [k], hq0⟩ := Subtype.ext hk'
        rw [e]
        exact hh.2.2 ⟨p' ++ [k], hq0⟩ ⟨k, rfl⟩

end WaveTurbulence.MainCoef
