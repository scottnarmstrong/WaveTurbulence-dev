/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Data
import Mathlib.Tactic

/-!
# Index counts for the exact snapshot-5 sumint datum

These elementary identities identify the dimension of the lattice input
and bound the number of blocks by the size in the source proposition.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- Every block has its distinguished zero slot. -/
theorem one_le_block_size (S : SumintShape) (i : Fin S.I) : 1 ≤ S.n i := by
  unfold SumintShape.n
  omega

/-- The bundled input index has exactly `M` elements. -/
theorem card_vector_index (S : SumintShape) : Fintype.card S.VIdx = S.M := by
  simp [SumintShape.VIdx, SumintShape.M, Fintype.card_sigma]

/-- The total number of input vectors controls the number of blocks. -/
theorem blocks_le_size (S : SumintShape) : S.I ≤ S.M := by
  calc
    S.I = ∑ _i : Fin S.I, 1 := by simp
    _ ≤ ∑ i, S.n i := sum_le_sum (fun i _ => one_le_block_size S i)
    _ = S.M := rfl

/-- The source assumption of at least one block implies a nonempty lattice input. -/
theorem size_pos (S : SumintShape) (hI : 0 < S.I) : 0 < S.M :=
  hI.trans_le (blocks_le_size S)

/-- There is one input time coordinate for each input vector coordinate. -/
theorem card_time_index (S : SumintShape) : Fintype.card S.TVar = S.M := by
  classical
  have hn : (∑ _i : {i : Fin S.I // S.nor i = true}, 3) =
      ∑ i : Fin S.I, if S.nor i then 3 else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin S.I => S.nor i = true))
      (by simp) (fun _ => (3 : ℕ))]
    rw [Finset.sum_filter]
  simp only [SumintShape.TVar, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  rw [hn]
  unfold SumintShape.M SumintShape.n
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  omega

end WaveTurbulence.SumintPar
