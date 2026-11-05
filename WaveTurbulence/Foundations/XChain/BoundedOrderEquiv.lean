/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerKernelSum
/-! An exact finite-range order label partitions any bounded-order source carrier. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def boundedOrderEquiv {α : Type*} (P : α → Prop) (order : α → ℕ) (M : ℕ) :
    (Σ n : Fin (M + 1), {a : α // P a ∧ order a = n.1}) ≃ {a : α // P a ∧ order a ≤ M} :=
  Equiv.ofBijective (fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.trans_le (Nat.le_of_lt_succ x.1.2)⟩) (by
    constructor
    · rintro ⟨n, a, ha, han⟩ ⟨m, b, hb, hbm⟩ he
      have hab : a = b := congrArg Subtype.val he
      cases hab
      have hnm : n = m := Fin.ext (han.symm.trans hbm)
      cases hnm
      rfl
    · rintro ⟨a, ha, hM⟩
      exact ⟨⟨⟨order a, Nat.lt_succ_of_le hM⟩, ⟨a, ha, rfl⟩⟩, rfl⟩)

end WaveTurbulence.Induct
