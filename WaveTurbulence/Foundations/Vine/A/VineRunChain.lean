/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineRunUnique
/-! The runs recorded in a skipped-ingredient decomposition are actual vine
chains. The atom sets are identified with the source ingredient splitting. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {N : Molecule V D} {S A L R : Finset V} {a b x y : V} {n : ℕ}

/-- The two declared runs inherit the genuine chain decomposition of the group. -/
theorem cut_runs_chain (H : SkelDecomp N S A L R a b x y)
    (hi : ChainIngredient N S a b n A x y) :
    (L = ∅ ∨ ∃ m, Chain N L a x m) ∧ (R = ∅ ∨ ∃ m, Chain N R y b m) := by
  obtain ⟨L', R', hS, hL, hR, hd⟩ := ingredient_runs H.mol hi H.hSB
  have K : SkelDecomp N S A L' R' a b x y := {
    mol := H.mol, hS := hS, hSB := H.hSB, hA := H.hA,
    hL := hL.imp id (fun ⟨hne, hB, _, hi⟩ => ⟨hne, hB, hi⟩),
    hR := hR.imp id (fun ⟨hne, hB, _, hi⟩ => ⟨hne, hB, hi⟩), hd := hd }
  obtain ⟨heL, heR⟩ := run_unique H K
  rw [heL, heR]
  exact ⟨hL.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2.2.1),
    hR.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2.2.1)⟩

omit [DecidableEq D] in
/-- A declared left run avoids the far joint of its containing group. -/
theorem cut_left_misses_end (H : SkelDecomp N S A L R a b x y) : b ∉ L := by
  intro hb
  rcases H.hR with ⟨_, hyb⟩ | ⟨_, hB, _⟩
  · have hyA := H.hA.2.2.1
    have hyL : y ∈ L := hyb.symm ▸ hb
    rcases H.hL with ⟨he, _⟩ | ⟨_, _, hi⟩
    · rw [he] at hyL; exact Finset.notMem_empty y hyL
    · have hz := mem_inter.mpr ⟨hyL, hyA⟩
      rw [hi, mem_singleton] at hz
      exact H.hA.2.2.2.1 hz.symm
  · exact (disjoint_left.mp H.hd hb) hB.2.2.1

omit [DecidableEq D] in
/-- A declared right run avoids the near joint of its containing group. -/
theorem cut_right_misses_start (H : SkelDecomp N S A L R a b x y) : a ∉ R :=
  cut_left_misses_end (reverseCut H)

end WaveTurbulence.VineA
