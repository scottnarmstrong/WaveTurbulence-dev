/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp17Suffix
public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone

/-! # Splitting a chain assembly at a piece (V5 Step 4b, step 4, WP-D)

For a chain assembly `B` with `n` pieces (piece `0` the bottom) and `1 ≤ k < n`: the upper block `Sk` (pieces `≥ k`, from `a` to the
lower joint `bk` of piece `k`) and the lower vine chain `Tk` (pieces `< k`, from `bk` to `b`), with `Sk ∩ Tk = {bk}`, `Sk ∪ Tk = U`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open Finset RegRed TTree WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
variable {w : ℕ} {G : Garden w}

theorem exists_split_assembly {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssembly G R n) : ∀ k : ℕ, 1 ≤ k → k < n → ∃ (Sk Tk : Finset (GBranch G.tree)) (bk : GBranch G.tree),
      G.molecule.IsBlock Sk a bk ∧ Vine.Chain G.molecule Tk bk b k ∧ Sk ∩ Tk = {bk} ∧ Sk ∪ Tk = U ∧
      (∀ j : Fin n, j.1 < k → (assemblyPieceAt B j).atoms ⊆ Tk) ∧
      (∀ j : Fin n, k ≤ j.1 → (assemblyPieceAt B j).atoms ⊆ Sk) ∧
      (∀ h : k < n, (assemblyPieceAt B ⟨k, h⟩).lower = bk) ∧
      (∀ j : Fin n, j.1 < k → (assemblyPieceAt B j).lower ≠ bk) := by
  induction B with
  | single hV R => intro k h1 h2; omega
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    intro k h1 h2
    have hn' : 0 < n' := B.length_pos
    have hch1 : Vine.Chain G.molecule T b' c' 1 := Vine.Chain.single ⟨X, hT⟩
    have hbc : b' ≠ c' := chain_joints_ne hch1
    have hjT := Vine.chain_joints_mem hch1
    have hSdeg := ((isBlock_iff_degree_connected _ _ _ _).mp B.isBlock).1
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      refine ⟨S, T, b', B.isBlock, hch1, hi, rfl, ?_, ?_, ?_, ?_⟩
      · intro j hj
        obtain rfl : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
        exact Finset.Subset.refl _
      · intro j hj
        refine Fin.cases (fun h => absurd h (by simp)) (fun j' _ => ?_) j hj
        exact assemblyPiece_subset B j'
      · intro h
        exact assemblyPiece_zero_lower B hn'
      · intro j hj
        obtain rfl : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
        exact hbc.symm
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      obtain ⟨Sk, Tk, bk, hSk, hTk, hint, hun, hat1, hat2, hlow, hne⟩ := ih (m + 1) (by omega) (by omega)
      have hTkS : Tk ⊆ S := hun ▸ Finset.subset_union_right
      have hSkS : Sk ⊆ S := hun ▸ Finset.subset_union_left
      have hSkdeg := ((isBlock_iff_degree_connected _ _ _ _).mp hSk).1
      have hTkj := Vine.chain_joints_mem hTk
      have hb'Tk : b' ∈ Tk := hTkj.2
      have hbkTk : bk ∈ Tk := hTkj.1
      have hbkSk : bk ∈ Sk := hSkdeg.2.2.1
      have hb'ne : b' ≠ bk := fun h => hne ⟨0, hn'⟩ (by simp) (by rw [assemblyPiece_zero_lower B hn']; exact h)
      have hb'Sk : b' ∉ Sk := fun h => hb'ne (by
        have : b' ∈ Sk ∩ Tk := mem_inter.mpr ⟨h, hb'Tk⟩
        rw [hint] at this; exact mem_singleton.mp this)
      have hTkT : Tk ∩ T = {b'} := by
        ext x
        constructor
        · intro hx
          have : x ∈ S ∩ T := mem_inter.mpr ⟨hTkS (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
          rwa [hi] at this
        · intro hx
          rw [mem_singleton] at hx; subst hx
          exact mem_inter.mpr ⟨hb'Tk, hjT.1⟩
      have hc'Sk : c' ∉ Sk := fun h => hbc (by
        have : c' ∈ S ∩ T := mem_inter.mpr ⟨hSkS h, hjT.2⟩
        rw [hi] at this; exact (mem_singleton.mp this).symm)
      have hbkc : bk ≠ c' := fun h => hc'Sk (h ▸ hbkSk)
      have hch : Vine.Chain G.molecule (Tk ∪ T) bk c' (m + 1 + 1) :=
        Vine.Chain.append hTk ⟨X, hT⟩ hTkT hbkc
      refine ⟨Sk, Tk ∪ T, bk, hSk, hch, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ext x
        constructor
        · intro hx
          obtain ⟨h1, h2⟩ := mem_inter.mp hx
          rcases mem_union.mp h2 with h | h
          · rw [← hint]; exact mem_inter.mpr ⟨h1, h⟩
          · exfalso
            have : x ∈ S ∩ T := mem_inter.mpr ⟨hSkS h1, h⟩
            rw [hi] at this
            exact hb'Sk (mem_singleton.mp this ▸ h1)
        · intro hx
          rw [mem_singleton] at hx; subst hx
          exact mem_inter.mpr ⟨hbkSk, mem_union_left _ hbkTk⟩
      · rw [← union_assoc, hun]
      · intro j hj
        refine Fin.cases (fun _ => ?_) (fun j' hj' => ?_) j hj
        · exact Finset.subset_union_right
        · exact (hat1 j' (by simp at hj'; omega)).trans Finset.subset_union_left
      · intro j hj
        refine Fin.cases (fun h => absurd h (by simp)) (fun j' hj' => ?_) j hj
        exact hat2 j' (by simp at hj'; omega)
      · intro h
        exact hlow (by omega)
      · intro j hj
        refine Fin.cases (fun _ => ?_) (fun j' hj' => ?_) j hj
        · exact fun h => hbkc h.symm
        · exact hne j' (by simp at hj'; omega)

end WaveTurbulence.VineEstS4
