/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeFlat
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeIntL

/-!
# The time domain of a tree with a lone leaf, as in the source

DH21 (varat) and Wave B's `kDomain` (with a lone leaf, (timepairtree)) state the time domain node by
node: `0 < t_𝔫 < u`, `t_{𝔫'} < t_𝔫` for a branching child `𝔫'`, and `t_𝔫 > s` if `𝔫` is the parent of
the lone leaf (at `lp`) (`treeDomFL`). It is the recursive domain `treeDomL` (`treeDomFL_eq`).
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree Set

/-- **The time domain of a tree with a lone leaf, node by node.** -/
def treeDomFL (T : TTree) (lp : Option TTree.Path) (s u : ℝ) : Set (TB T → ℝ) :=
  {τ | LoneOK lp s u ∧ ∀ p, 0 < τ p ∧ τ p < u ∧ (∀ q : TB T, q.IsChild p → τ q < τ p) ∧
    ∀ i : Fin 3, lp = some (p.1 ++ [i]) → s < τ p}

theorem subLone_eq_some {lp : Option TTree.Path} {i : Fin 3} {q : TTree.Path} :
    subLone lp i = some q ↔ lp = some (i :: q) := by
  rcases lp with _ | _ | ⟨j, p⟩
  · simp [subLone]
  · simp [subLone]
  · simp only [subLone]
    split_ifs with h
    · subst h; simp
    · simp only [false_iff, Option.some.injEq, List.cons.injEq, not_and]
      exact fun h' => absurd h' h

theorem treeDomFL_eq : ∀ (T : TTree) (lp : Option TTree.Path) (s u : ℝ),
    treeDomFL T lp s u = treeDomL T lp s u
  | .leaf, lp, s, u => by
    ext τ
    simp only [treeDomFL, treeDomL, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun _ p => absurd p.2 (not_mem_branching_leaf _)
  | .node l m r, lp, s, u => by
    ext τ
    rw [treeDomL, Set.mem_ofPred_eq, ← treeDomFL_eq l, ← treeDomFL_eq m, ← treeDomFL_eq r]
    have hroot : tRoot τ = τ (TB.root l m r) := rfl
    constructor
    · rintro ⟨hL, h⟩
      have hbelow : ∀ (i : Fin 3) (q : TTree.Path) (hq : i :: q ∈ (TTree.node l m r).branching),
          τ ⟨i :: q, hq⟩ < tRoot τ := by
        intro i q hq
        have h0 : [i] ∈ (TTree.node l m r).branching :=
          mem_branching_of_prefix _ [i] q hq
        have h1 := le_of_prefix (fun p q hqp => (h p).2.2.1 q hqp) ⟨[i], h0⟩ q hq
        have h2 := (h (TB.root l m r)).2.2.1 ⟨[i], h0⟩ ⟨i, rfl⟩
        exact h1.trans_lt h2
      have hsubt : ∀ i : Fin 3, restrT i τ ∈
          treeDomFL (tchild (TTree.node l m r) i) (subLone lp i) s (tRoot τ) := by
        intro i
        refine ⟨fun hs => ?_, fun q => ⟨(h _).1, hbelow i q.1 _, fun q' ⟨k, hk⟩ => (h _).2.2.1 _ ⟨k, ?_⟩,
          fun k hk => (h _).2.2.2 k ?_⟩⟩
        · rw [subLone_eq_some] at hs
          exact (h (TB.root l m r)).2.2.2 i (by simpa [TB.root] using hs)
        · simp [TB.sub, hk]
        · rw [subLone_eq_some] at hk
          simpa [TB.sub] using hk
      exact ⟨hL, (h _).1, (h _).2.1, hsubt 0, hsubt 1, hsubt 2⟩
    · rintro ⟨hL, h0, hu, hl, hm, hr⟩
      have hsubt : ∀ i : Fin 3, restrT i τ ∈
          treeDomFL (tchild (TTree.node l m r) i) (subLone lp i) s (tRoot τ) := by
        intro i
        fin_cases i
        · exact hl
        · exact hm
        · exact hr
      refine ⟨hL, ?_⟩
      rintro ⟨_ | ⟨i, p'⟩, hp⟩
      · refine ⟨h0, hu, fun q ⟨k, hk⟩ => ?_, fun k hk => ?_⟩
        · have hk' : q.1 = k :: [] := by simpa using hk
          have hq0 : ([] : TTree.Path) ∈ (tchild (TTree.node l m r) k).branching :=
            (cons_mem_branching_node l m r k []).1 (hk' ▸ q.2)
          have := (hsubt k).2 ⟨[], hq0⟩
          have e : q = TB.sub l m r k ⟨[], hq0⟩ := Subtype.ext hk'
          rw [e]
          exact this.2.1
        · exact (hsubt k).1 (subLone_eq_some.2 (by simpa using hk))
      · have hp' : p' ∈ (tchild (TTree.node l m r) i).branching :=
          (cons_mem_branching_node l m r i p').1 hp
        have hh := (hsubt i).2 ⟨p', hp'⟩
        refine ⟨hh.1, hh.2.1.trans hu, fun q ⟨k, hk⟩ => ?_, fun k hk => hh.2.2.2 k ?_⟩
        · have hk' : q.1 = i :: (p' ++ [k]) := by simpa using hk
          have hq0 : p' ++ [k] ∈ (tchild (TTree.node l m r) i).branching :=
            (cons_mem_branching_node l m r i _).1 (hk' ▸ q.2)
          have e : q = TB.sub l m r i ⟨p' ++ [k], hq0⟩ := Subtype.ext hk'
          rw [e]
          exact hh.2.2.1 ⟨p' ++ [k], hq0⟩ ⟨k, rfl⟩
        · exact subLone_eq_some.2 (by simpa using hk)

end WaveTurbulence.MainCoef
