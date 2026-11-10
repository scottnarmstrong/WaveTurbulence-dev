/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeBottom

/-!
# Prop 6.1, `q > q'`, trees: the induction over the blocks of the chain

**`tree_lower_bounds`**: for every lower state of a coherent tree (a suffix `Y` of its chain, below `(0, π)` in
layer `u`), on any target box mapped into the unit box by `ts ↦ ts + (b₀, -q')`, the error and the lower leading
term of the lower tree at `t = u + 1` satisfy `≤ 3^{m+1} M₀ D₀^m δ^m Λ β` and `≤ M₀ D₀^m δ^m β` with
`M₀ = K_tr C²`, `D₀ = 2C⁴`, `β = ∏ B_leaf`. The base case is a single block (the lone leaf in layer `q' ≤ u`):
the bottom trace (`tree_bottom_bounds`). The step removes the top block (`tree_block_step`, `restr_step`).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem appendChain_nil_right : ∀ X : RegChain, appendChain X .nil = X
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    show RegChain.pair m Qr Qg inner (appendChain rest .nil) = _
    rw [appendChain_nil_right rest]

theorem snd_le_of_unitBox {b₀ : ℝ} {q' : ℕ} {ts : Fin 2 → ℝ}
    (h : ts + ![b₀, -(q' : ℝ)] ∈ (Layered.unitBox : Set (Fin 2 → ℝ))) : ts 1 ≤ (q' : ℝ) + 1 := by
  have h1 := (h 1).2
  have e : (ts + ![b₀, -(q' : ℝ)]) 1 = ts 1 - q' := by simp; ring
  rw [e] at h1
  linarith

section Induction

variable (P : WTParams) {p : ℕ} {C : ℝ} (O : Oracle P p C) (hC : 1 ≤ C)
  (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη0 : 0 ≤ P.η) (hη1 : P.η ≤ 1) (hη2 : P.η ≤ 1 - P.η) (hδ : 0 ≤ P.δ)
  (hΛ0 : 0 ≤ gainΛ P) (hΛ1 : gainΛ P ≤ 1)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 P.d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q) (hqp : q ≤ p)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hη0 hη1 hη2 hδ hΛ0 hΛ1 F hqq hqp hT'

end Induction

end WaveTurbulence.PL234
