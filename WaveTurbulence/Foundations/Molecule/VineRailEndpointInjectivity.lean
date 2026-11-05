/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailIndex
import Mathlib.Tactic

/-! # Distinctness of both full rails including their old endpoint pairs -/

public section
namespace WaveTurbulence.Vine

/-- A rail with two distinct old endpoints and fresh interior is injective
on all its available coordinates, including both endpoints. -/
theorem railAtom_full_injective (N a b k : ℕ) (ha : a<N) (hb : b<N) (hab : a ≠ b) :
    Function.Injective (fun i : Fin (k+2) => railAtom N a b k i.1) := by
  intro i j he
  apply Fin.ext
  dsimp only at he
  unfold railAtom at he
  split_ifs at he <;> omega

/-- The two full rails are disjoint when their four old endpoints are
cross-distinct and both allocations start beyond all old endpoints. -/
theorem railAtom_full_cross (N a b c d k : ℕ)
    (ha : a<N) (hb : b<N) (hc : c<N) (hd : d<N)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (i j : Fin (k+2)) : railAtom N a b k i.1 ≠ railAtom (N+k) c d k j.1 := by
  intro he
  unfold railAtom at he
  split_ifs at he <;> omega

/-- Both rails together are injective on all old endpoints and fresh rungs. -/
theorem railAtom_full_pair_injective (N a b c d k : ℕ)
    (ha : a<N) (hb : b<N) (hc : c<N) (hd : d<N)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Function.Injective (Sum.elim (fun i : Fin (k+2) => railAtom N a b k i.1)
      (fun i : Fin (k+2) => railAtom (N+k) c d k i.1)) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (railAtom_full_injective N a b k ha hb hab he)
    | inr j => exact False.elim (railAtom_full_cross N a b c d k ha hb hc hd hac had hbc hbd i j he)
  | inr i =>
    cases j with
    | inl j => exact False.elim (railAtom_full_cross N a b c d k ha hb hc hd hac had hbc hbd j i he.symm)
    | inr j =>
      have hc' : c<N+k := by omega
      have hd' : d<N+k := by omega
      exact congrArg Sum.inr (railAtom_full_injective (N+k) c d k hc' hd' hcd he)

end WaveTurbulence.Vine
