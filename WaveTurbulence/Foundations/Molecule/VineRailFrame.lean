/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRailEndpointInjectivity
import Mathlib.Tactic

/-! # Fresh rail atoms are separated from the opposite complete rail -/

public section
namespace WaveTurbulence.Vine

/-- A fresh upper atom differs from every opposite-rail atom, even when
some old port of the two rails coincides. -/
theorem railAtom_fresh_upper_cross (N a b c d k i j : ℕ)
    (_ha : a<N) (_hb : b<N) (hc : c<N) (hd : d<N)
    (hi : 1 ≤ i) (hin : i ≤ k) :
    railAtom N a b k i ≠ railAtom (N+k) c d k j := by
  rw [railAtom_interior N a b k i hi hin]
  unfold railAtom
  split_ifs <;> omega

/-- The analogous separation for a fresh lower atom. -/
theorem railAtom_fresh_lower_cross (N a b c d k i j : ℕ)
    (ha : a<N) (hb : b<N) (_hc : c<N) (_hd : d<N)
    (hi : 1 ≤ i) (hin : i ≤ k) :
    railAtom (N+k) c d k i ≠ railAtom N a b k j := by
  rw [railAtom_interior (N+k) c d k i hi hin]
  unfold railAtom
  split_ifs <;> omega

end WaveTurbulence.Vine
