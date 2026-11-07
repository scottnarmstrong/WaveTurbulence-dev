/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSpine
public import WaveTurbulence.Foundations.FinalCount.RedSpliceIngr
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.Molecule.VineSizeFormulas
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-E: the pieces of a chain assembly are the members of its spine; vine type parity

`assemblyPieces_spine`: for a data-bearing chain assembly `B` of a block `U` between `a` and `b`, the atom sets of its pieces
are exactly the atom sets of the members of a spine of `U` (so, by `Spine.unique`, of THE spine).
`isBad_iff_even`: the bad/normal type of a vine is determined by the parity of its atom count.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.VineEstS2 WaveTurbulence.Vine
  WaveTurbulence.RegRed

variable {w : ℕ}

theorem assemblyPieces_spine {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) :
    ∃ L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree), Spine G.molecule L U a b ∧
      L.length = n ∧ (∀ i : Fin n, ∃ p q, ((assemblyPieceAt B i).atoms, p, q) ∈ L) ∧
      (∀ T p q, (T, p, q) ∈ L → ∃ i : Fin n, (assemblyPieceAt B i).atoms = T) := by
  induction B with
  | @single U a b X hV R =>
    refine ⟨_, Spine.one ⟨_, hV⟩, rfl, fun i => ⟨a, b, by simp [assemblyPieceAt]⟩, ?_⟩
    intro T p q hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, -, -⟩ := hm
    exact ⟨0, rfl⟩
  | @append S T a b c n RP B X hT hi hU R ih =>
    obtain ⟨L, hs, hl, h1, h2⟩ := ih
    refine ⟨L ++ [(T, b, c)], Spine.snoc hs ⟨_, hT⟩ hi hU.2.2.2.1, by simp [hl], ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨b, c, by simp [assemblyPieceAt]⟩
      · obtain ⟨p, q, hpq⟩ := h1 j
        exact ⟨p, q, List.mem_append_left _ (by simpa [assemblyPieceAt] using hpq)⟩
    · intro T' p q hm
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨i, hi'⟩ := h2 T' p q h
        exact ⟨i.succ, by simpa [assemblyPieceAt] using hi'⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        exact ⟨0, by simp [assemblyPieceAt]⟩

theorem isBad_iff_even {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (h : M.IsVine X S a b) : X.IsBad = true ↔ Even S.card := by
  obtain ⟨-, k, hk, f, hinj, himg, -, -⟩ := h
  have hc : S.card = (X.expand k).n := by
    rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]
  have h2 := expand_atoms_groups X k hk
  rw [hc, h2]
  cases hX : X.IsBad
  · simp [Nat.even_add]
    decide
  · simp [Nat.even_add]

theorem isBad_unique {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X Y : VineType}
    {S : Finset V} {a b c e : V} (hX : M.IsVine X S a b) (hY : M.IsVine Y S c e) : X.IsBad = Y.IsBad := by
  exact Bool.eq_iff_iff.mpr ((isBad_iff_even hX).trans (isBad_iff_even hY).symm)

end WaveTurbulence.Represents
