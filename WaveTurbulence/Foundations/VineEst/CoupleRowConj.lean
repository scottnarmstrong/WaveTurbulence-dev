/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.GateRows
public import WaveTurbulence.Foundations.VineEst.ConjCoherent
public import WaveTurbulence.Foundations.VineEst.NormSwapConj

/-!
# The `q < q'` orientation of a coherent couple row (CONJ-COH; ruling R20(5))

`couple_row_le` (V5 `GateRows`) bounds the starred kernel of a regular couple of incoherency index `0` only for
`q' ≤ q`, the orientation of the 0814 gate.  For `q ≤ q'` the conjugate couple (`conjCpl Q`, `LGbar`) is coherent at
`(p, q', q)` (`isCoherentCoupleAt_conj`) and `K*_{LG}(t, s) = conj K*_{LGbar}(s, t)` (`KQstar_conj`), so by the
swap-and-conjugate invariance of `XNormRestr` (`XNormRestr_swapConj`) the bound for `(q, q')` follows from the bound
for `(q', q)` applied to the conjugate.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

namespace WaveTurbulence.ConjCoh

open WaveTurbulence WaveTurbulence.VineEstS3 WaveTurbulence.LGSpine WaveTurbulence.PL234

theorem timeBox_permT (q q' : ℝ) :
    permT (Equiv.swap (0 : Fin 2) 1) ⁻¹' timeBox q q' = timeBox q' q := by
  ext ts
  simp [timeBox, permT, and_comm]

theorem swap_invol : ∀ i : Fin 2, (Equiv.swap (0 : Fin 2) 1) ((Equiv.swap (0 : Fin 2) 1) i) = i := fun i => by
  simp

/-- The restriction norm of the starred kernel of `LG` over `ℬ(q, q')` is that of the conjugate garden over
`ℬ(q', q)`. -/
theorem XNormRestr_KQstar_conj {LG LGbar : LayeredGarden 2} (h : IsConjugateCouple LG LGbar)
    (θ : ℝ) (Λ₁ Λ₂ : ℕ) (q q' : ℝ) (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ) :
    XNormRestr θ Λ₁ Λ₂ (timeBox q q') Set.univ (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) =
      XNormRestr θ Λ₁ Λ₂ (timeBox q' q) Set.univ (fun ts k => KQstar L γ δ F LGbar (ts 0) (ts 1) k) := by
  have hf : (fun (ts : Fin 2 → ℝ) (k : Mom d) => KQstar L γ δ F LG (ts 0) (ts 1) k) =
      swapConj (Equiv.swap (0 : Fin 2) 1) (fun ts k => KQstar L γ δ F LGbar (ts 0) (ts 1) k) := by
    funext ts k
    have := KQstar_conj L γ δ F h (ts 1) (ts 0) k
    simp only [swapConj, permT]
    simp [this]
  rw [hf, XNormRestr_swapConj swap_invol, timeBox_permT]


end WaveTurbulence.ConjCoh
