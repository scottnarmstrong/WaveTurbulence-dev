/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceSlotCounts
/-! A uniform exponential bound for actual replacement data at a fixed nonzero garden order. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Reg.Skeleton

theorem source_reconstruction_data_exponential {R n : ℕ} (S : Garden (2 * R))
    (hS : S.IsPlain) (hn : 1 ≤ n) (hord : S.order ≤ n) (hR : R ≤ n + 1) :
    Nat.card {D : ReconstructionData S // D.size ≤ n} ≤ (12 ^ 18) ^ n := by
  apply (reconstructionDataCount_uniform S hS n hord).trans
  rw [← pow_mul, ← pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 12)
  omega

end WaveTurbulence.LGSpine
