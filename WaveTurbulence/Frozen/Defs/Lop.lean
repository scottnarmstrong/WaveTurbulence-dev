/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ANonlin
public import WaveTurbulence.Frozen.Defs.Slot
public import WaveTurbulence.Frozen.Defs.SlotCountB
public import WaveTurbulence.Frozen.Defs.SlotOrder
public import WaveTurbulence.Frozen.Defs.TreeTermN

/-!
# Lop

Wave B tier B1 (WaveB1-System.lean), source: L717–L725; WAVE-B §2.5.2. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- **The operators `ℒ_j`** (T (eqnbk1.5), L717–L725; WAVE-B §2.5.2): `(ℒ_j b)_n(t) =
∑_{(j)} ∫_p^t 𝒞₊(u, v̄, w)_n(s) ds` over `(u,v,w) ∈ {b, 𝒥₀, …, 𝒥_{Ntr}}³` with exactly `j` entries
equal to `b`, and for `j = 0` the restriction `n₁ + n₂ + n₃ ≥ Ntr`; the conjugate in the middle slot
is explicit (F9). `b` is a function on `[p, p+1]`, extended to `ℝ` by `Set.IccExtend` (only its values
on `[p, t]` are used). -/
noncomputable def Lop (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (j : ℕ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  let val : Slot Ntr → ℝ → (Fin d → ℤ) → ℂ := fun o s => match o with
    | none => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s
    | some N => treeTermN L γ δ p N aP s
  ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)),
    ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (val x.1 s)
      (fun m => (starRingEnd ℂ) (val x.2.1 s m)) (val x.2.2 s) n

end Duhamel
end WaveTurbulence
