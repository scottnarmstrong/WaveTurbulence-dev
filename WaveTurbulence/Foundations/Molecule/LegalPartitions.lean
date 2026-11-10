/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # Noncrossing pair partitions (DH21 Definition 4.4, Proposition 4.5)

Labels are zero-based; the paper's label j corresponds to j - 1 here.
-/

@[expose] public section

namespace WaveTurbulence.Reg

/-- A partition of an ordered finite set into pairs, represented by its partner involution. -/
structure PairPartition (n : ℕ) where
  pair : Fin n → Fin n
  involutive : Function.Involutive pair
  no_fixed : ∀ a, pair a ≠ a

namespace PairPartition
variable {n : ℕ} (P : PairPartition n)

/-- DH21's legality condition: distinct pairs do not interlace. -/
def Legal : Prop := ∀ a b c d : Fin n, a < b → b < c → c < d →
  P.pair a = c → P.pair b = d → False

instance : Decidable P.Legal := by unfold Legal; infer_instance

end PairPartition
end WaveTurbulence.Reg
